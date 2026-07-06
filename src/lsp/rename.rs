use async_lsp::lsp_types::{TextEdit, Url, WorkspaceEdit};
use derive_visitor::{Drive, Visitor};
use rustc_hash::FxHashSet;

use crate::analysis::workspace::Workspace as AnalysisWorkspace;
use crate::analysis::{node_ids_at_offset, span_contains};
use crate::lexer::Lexer;
use crate::name_resolution::symbol::{EffectId, Symbol};
use crate::node_kinds::{
    decl::Decl,
    expr::Expr,
    func::Func,
    func_signature::FuncSignature,
    generic_decl::GenericDecl,
    parameter::Parameter,
    pattern::{Pattern, RecordFieldPattern},
    stmt::Stmt,
    type_annotation::TypeAnnotation,
};
use crate::token_kind::TokenKind;

use super::server::{byte_span_to_range_utf16, document_id_for_uri, url_from_document_id};

fn is_valid_identifier(name: &str) -> bool {
    let mut lexer = Lexer::new(name);
    let Ok(token) = lexer.next() else {
        return false;
    };
    if token.kind != TokenKind::Identifier {
        return false;
    }
    matches!(lexer.next().ok().map(|t| t.kind), Some(TokenKind::EOF))
}

fn is_symbol_renamable(module: &AnalysisWorkspace, symbol: Symbol) -> bool {
    use crate::name_resolution::symbol::{
        AssociatedTypeId, EnumId, GlobalId, InstanceMethodId, MethodRequirementId, PropertyId,
        ProtocolId, StaticMethodId, StructId, TypeAliasId, VariantId,
    };

    match symbol {
        Symbol::Builtin(..)
        | Symbol::Main
        | Symbol::Library
        | Symbol::Synthesized(..)
        | Symbol::Initializer(..) => false,

        Symbol::Struct(StructId { module_id, .. })
        | Symbol::Enum(EnumId { module_id, .. })
        | Symbol::TypeAlias(TypeAliasId { module_id, .. })
        | Symbol::Global(GlobalId { module_id, .. })
        | Symbol::Property(PropertyId { module_id, .. })
        | Symbol::InstanceMethod(InstanceMethodId { module_id, .. })
        | Symbol::StaticMethod(StaticMethodId { module_id, .. })
        | Symbol::Variant(VariantId { module_id, .. })
        | Symbol::Protocol(ProtocolId { module_id, .. })
        | Symbol::AssociatedType(AssociatedTypeId { module_id, .. })
        | Symbol::Effect(EffectId { module_id, .. })
        | Symbol::MethodRequirement(MethodRequirementId { module_id, .. }) => {
            module_id == module.local_module_id
        }

        Symbol::TypeParameter(..)
        | Symbol::DeclaredLocal(..)
        | Symbol::PatternBindLocal(..)
        | Symbol::ParamLocal(..) => true,
    }
}

pub fn rename_at(
    module: &AnalysisWorkspace,
    uri: &Url,
    byte_offset: u32,
    new_name: &str,
) -> Option<WorkspaceEdit> {
    if !is_valid_identifier(new_name) {
        return None;
    }

    let symbol = rename_symbol_at_offset(module, uri, byte_offset)?;
    if !is_symbol_renamable(module, symbol) {
        return None;
    }

    let mut changes: std::collections::HashMap<Url, Vec<TextEdit>> = Default::default();
    for (idx, doc_id) in module.file_id_to_document.iter().enumerate() {
        let Some(file_uri) = url_from_document_id(doc_id) else {
            continue;
        };
        let text = module.texts.get(idx)?;
        let Some(ast) = module.asts.get(idx).and_then(|a| a.as_ref()) else {
            continue;
        };
        let spans = rename_spans_in_ast(module, ast, symbol);

        let mut edits: Vec<TextEdit> = spans
            .into_iter()
            .filter_map(|(start, end)| {
                let range = byte_span_to_range_utf16(text, start, end)?;
                Some(TextEdit::new(range, new_name.to_string()))
            })
            .collect();

        if edits.is_empty() {
            continue;
        }

        edits.sort_by_key(|edit| (edit.range.start.line, edit.range.start.character));
        changes.insert(file_uri, edits);
    }

    if changes.is_empty() {
        return None;
    }

    Some(WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    })
}

fn rename_symbol_at_offset(
    module: &AnalysisWorkspace,
    uri: &Url,
    byte_offset: u32,
) -> Option<Symbol> {
    let document_id = document_id_for_uri(uri);
    let file_id = *module.document_to_file_id.get(&document_id)?;
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|a| a.as_ref())?;
    for root in &ast.roots {
        let crate::node::Node::Decl(decl) = root else {
            continue;
        };
        if let Some(symbol) = goto_definition_symbol_from_decl(decl, byte_offset)
            .or_else(|| imported_symbol_at_offset(module, &ast.path, decl, byte_offset))
        {
            return Some(symbol);
        }
    }

    let candidate_ids = node_ids_at_offset(ast, byte_offset);

    for node_id in candidate_ids {
        let Some(node) = ast.find(node_id) else {
            continue;
        };

        let symbol = match node {
            crate::node::Node::Expr(expr) => rename_symbol_from_expr(module, &expr, byte_offset),
            crate::node::Node::Stmt(stmt) => rename_symbol_from_stmt(module, &stmt, byte_offset),
            crate::node::Node::TypeAnnotation(ty) => {
                goto_definition_symbol_from_type_annotation(module, &ty, byte_offset)
            }
            crate::node::Node::Decl(decl) => goto_definition_symbol_from_decl(&decl, byte_offset)
                .or_else(|| imported_symbol_at_offset(module, &ast.path, &decl, byte_offset)),
            crate::node::Node::Parameter(param) => {
                if span_contains(param.name_span, byte_offset) {
                    param.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::Func(func) => {
                if span_contains(func.name_span, byte_offset) {
                    func.name.symbol().ok()
                } else {
                    effect_symbol_at_offset(&func.effects, byte_offset)
                }
            }
            crate::node::Node::FuncSignature(sig) => {
                let meta = ast.meta.get(&sig.id)?;
                let (start, end) = meta.identifiers.first().map(|t| (t.start, t.end))?;
                if start <= byte_offset && byte_offset <= end {
                    sig.name.symbol().ok()
                } else {
                    effect_symbol_at_offset(&sig.effects, byte_offset)
                }
            }
            crate::node::Node::GenericDecl(generic) => {
                if span_contains(generic.name_span, byte_offset) {
                    generic.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::Pattern(pattern) => match &pattern.kind {
                crate::node_kinds::pattern::PatternKind::Bind(name) => {
                    let meta = ast.meta.get(&pattern.id)?;
                    let (start, end) = identifier_span_at_offset(meta, byte_offset)?;
                    if start <= byte_offset && byte_offset <= end {
                        name.symbol().ok()
                    } else {
                        None
                    }
                }
                crate::node_kinds::pattern::PatternKind::Variant {
                    variant_name_span, ..
                } => {
                    if span_contains(*variant_name_span, byte_offset) {
                        symbol_for_member_resolution(
                            module.types.member_resolutions.get(&pattern.id),
                        )
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        };

        if symbol.is_some() {
            return symbol;
        }
    }

    None
}

fn rename_symbol_from_expr(
    module: &AnalysisWorkspace,
    expr: &crate::node_kinds::expr::Expr,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::expr::ExprKind;

    match &expr.kind {
        ExprKind::Variable(name) | ExprKind::Constructor(name) => name.symbol().ok(),
        ExprKind::Call { callee, args, .. } => {
            if span_contains(callee.span, byte_offset) {
                rename_symbol_from_expr(module, callee, byte_offset)
            } else {
                construction_arg_symbol_at_offset(module, callee, args, byte_offset)
            }
        }
        ExprKind::Member(_, _, label_span) => {
            if !span_contains(*label_span, byte_offset) {
                return None;
            }
            symbol_for_member_resolution(module.types.member_resolutions.get(&expr.id))
        }
        ExprKind::CallEffect {
            effect_name,
            effect_name_span,
            ..
        } => {
            if !effect_span_contains(*effect_name_span, byte_offset) {
                return None;
            }
            effect_name.symbol().ok()
        }
        _ => None,
    }
}

fn construction_arg_symbol_at_offset(
    module: &AnalysisWorkspace,
    callee: &crate::node_kinds::expr::Expr,
    args: &[crate::node_kinds::call_arg::CallArg],
    byte_offset: u32,
) -> Option<Symbol> {
    let struct_info = module
        .types
        .catalog
        .structs
        .get(&construction_callee_symbol(callee)?)?;
    args.iter().find_map(|arg| {
        if span_contains(arg.label_span, byte_offset) {
            struct_info
                .fields
                .get(&arg.label.to_string())
                .map(|(symbol, _)| *symbol)
        } else {
            None
        }
    })
}

fn construction_callee_symbol(callee: &crate::node_kinds::expr::Expr) -> Option<Symbol> {
    use crate::node_kinds::expr::ExprKind;

    match &callee.kind {
        ExprKind::Constructor(name) | ExprKind::Variable(name) => name.symbol().ok(),
        _ => None,
    }
}

fn symbol_for_member_resolution(
    resolution: Option<&crate::types::output::MemberResolution>,
) -> Option<Symbol> {
    match resolution? {
        crate::types::output::MemberResolution::Direct(symbol) => Some(*symbol),
        crate::types::output::MemberResolution::ViaConformance { witness, .. } => Some(*witness),
    }
}

fn rename_symbol_from_stmt(
    module: &AnalysisWorkspace,
    stmt: &crate::node_kinds::stmt::Stmt,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::stmt::StmtKind;

    match &stmt.kind {
        StmtKind::Expr(expr) => span_contains(expr.span, byte_offset)
            .then(|| rename_symbol_from_expr(module, expr, byte_offset))?,
        StmtKind::Return(Some(expr)) => span_contains(expr.span, byte_offset)
            .then(|| rename_symbol_from_expr(module, expr, byte_offset))?,
        StmtKind::If(cond, ..) => span_contains(cond.span, byte_offset)
            .then(|| rename_symbol_from_expr(module, cond, byte_offset))?,
        StmtKind::Loop(Some(cond), ..) => span_contains(cond.span, byte_offset)
            .then(|| rename_symbol_from_expr(module, cond, byte_offset))?,
        StmtKind::Assignment(lhs, rhs) => {
            if span_contains(lhs.span, byte_offset) {
                rename_symbol_from_expr(module, lhs, byte_offset)
            } else if span_contains(rhs.span, byte_offset) {
                rename_symbol_from_expr(module, rhs, byte_offset)
            } else {
                None
            }
        }
        StmtKind::For { iterable, .. } => span_contains(iterable.span, byte_offset)
            .then(|| rename_symbol_from_expr(module, iterable, byte_offset))?,
        StmtKind::Continue(Some(expr)) => span_contains(expr.span, byte_offset)
            .then(|| rename_symbol_from_expr(module, expr, byte_offset))?,
        StmtKind::Handling {
            effect_name,
            effect_name_span,
            ..
        } => {
            if !effect_span_contains(*effect_name_span, byte_offset) {
                return None;
            }
            effect_name.symbol().ok()
        }
        _ => None,
    }
}

fn goto_definition_symbol_from_type_annotation(
    module: &AnalysisWorkspace,
    ty: &crate::node_kinds::type_annotation::TypeAnnotation,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    match &ty.kind {
        TypeAnnotationKind::Borrow { inner, .. } | TypeAnnotationKind::Unique { inner } => {
            goto_definition_symbol_from_type_annotation(module, inner, byte_offset)
        }
        TypeAnnotationKind::Nominal {
            name, name_span, ..
        } => {
            if !nominal_name_span_contains(name, *name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        TypeAnnotationKind::Any {
            protocol,
            assoc_bindings,
        } => goto_definition_symbol_from_type_annotation(module, protocol, byte_offset).or_else(
            || {
                assoc_bindings.iter().find_map(|binding| {
                    if span_contains(binding.name_span, byte_offset) {
                        symbol_for_any_assoc_binding(module, protocol, binding)
                    } else {
                        goto_definition_symbol_from_type_annotation(
                            module,
                            &binding.value,
                            byte_offset,
                        )
                    }
                })
            },
        ),
        TypeAnnotationKind::NominalPath {
            base,
            member,
            member_span,
            ..
        } => {
            if span_contains(*member_span, byte_offset) {
                symbol_for_associated_type_member(module, base, member)
            } else {
                goto_definition_symbol_from_type_annotation(module, base, byte_offset)
            }
        }
        _ => None,
    }
}

fn goto_definition_symbol_from_decl(
    decl: &crate::node_kinds::decl::Decl,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::decl::DeclKind;

    match &decl.kind {
        DeclKind::Struct {
            name, name_span, ..
        }
        | DeclKind::Protocol {
            name, name_span, ..
        }
        | DeclKind::Extend {
            name, name_span, ..
        }
        | DeclKind::Enum {
            name, name_span, ..
        }
        | DeclKind::Property {
            name, name_span, ..
        }
        | DeclKind::Effect {
            name, name_span, ..
        } => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        DeclKind::TypeAlias(name, name_span, ..) => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        DeclKind::EnumVariant {
            name, name_span, ..
        } => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        _ => None,
    }
}

fn imported_symbol_at_offset(
    module: &AnalysisWorkspace,
    source_path: &str,
    decl: &crate::node_kinds::decl::Decl,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::decl::{DeclKind, ImportedSymbols};

    let DeclKind::Import(import) = &decl.kind else {
        return None;
    };

    let ImportedSymbols::Named(imported_symbols) = &import.symbols else {
        return None;
    };

    let imported = imported_symbols
        .iter()
        .find(|imported| span_contains(imported.span, byte_offset))?;

    symbol_exported_by_import(module, source_path, import, &imported.name)
}

fn symbol_exported_by_import(
    module: &AnalysisWorkspace,
    source_path: &str,
    import: &crate::node_kinds::decl::Import,
    name: &str,
) -> Option<Symbol> {
    let target_file_id = target_file_id_for_import(module, source_path, &import.path)?;
    let target_scope_id = crate::node_id::NodeID(target_file_id, 0);
    let target_scope = module.resolved_names.scopes.get(&target_scope_id)?;

    target_scope
        .types
        .get(name)
        .or_else(|| target_scope.values.get(name))
        .copied()
}

fn target_file_id_for_import(
    module: &AnalysisWorkspace,
    source_path: &str,
    import_path: &crate::node_kinds::decl::ImportPath,
) -> Option<crate::node_id::FileID> {
    use crate::node_kinds::decl::ImportPath;

    let target_path = match import_path {
        ImportPath::Relative(rel_path) => {
            let source_path = std::path::Path::new(source_path);
            let source_dir = source_path.parent()?;
            let clean_rel = rel_path.strip_prefix("./").unwrap_or(rel_path);
            source_dir.join(clean_rel)
        }
        ImportPath::Package(_) => return None,
    };

    let target_uri = Url::from_file_path(target_path).ok()?;
    let target_doc_id = document_id_for_uri(&target_uri);
    module.document_to_file_id.get(&target_doc_id).copied()
}

fn identifier_span_at_offset(
    meta: &crate::node_meta::NodeMeta,
    byte_offset: u32,
) -> Option<(u32, u32)> {
    meta.identifiers
        .iter()
        .find(|tok| tok.start <= byte_offset && byte_offset <= tok.end)
        .map(|tok| (tok.start, tok.end))
}

fn nominal_name_span_contains(
    name: &crate::name::Name,
    name_span: crate::span::Span,
    byte_offset: u32,
) -> bool {
    if span_contains(name_span, byte_offset) {
        return true;
    }

    let name = name.name_str();
    if !name.contains("::") || name.starts_with('.') {
        return false;
    }

    let qualified_end = name_span.start.saturating_add(name.len() as u32);
    name_span.start <= byte_offset && byte_offset <= qualified_end
}

fn symbol_for_any_assoc_binding(
    module: &AnalysisWorkspace,
    protocol: &crate::node_kinds::type_annotation::TypeAnnotation,
    binding: &crate::node_kinds::type_annotation::AnyAssocBinding,
) -> Option<Symbol> {
    let crate::node_kinds::type_annotation::TypeAnnotationKind::Nominal { name, .. } =
        &protocol.kind
    else {
        return None;
    };
    let protocol = name.symbol().ok()?;
    module
        .types
        .catalog
        .associated_type_in(protocol, &binding.name.name_str())
        .map(|(_, assoc)| assoc)
}

fn symbol_for_associated_type_member(
    module: &AnalysisWorkspace,
    base: &crate::node_kinds::type_annotation::TypeAnnotation,
    member: &crate::label::Label,
) -> Option<Symbol> {
    let label = member.to_string();
    let base_symbol = match &base.kind {
        crate::node_kinds::type_annotation::TypeAnnotationKind::Nominal { name, .. }
        | crate::node_kinds::type_annotation::TypeAnnotationKind::SelfType(name) => {
            name.symbol().ok()?
        }
        _ => return None,
    };

    if let Some(info) = module.types.catalog.protocols.get(&base_symbol) {
        return info.assoc.get(&label).copied().or_else(|| {
            module
                .types
                .catalog
                .associated_type_in(base_symbol, &label)
                .map(|(_, assoc)| assoc)
        });
    }

    module
        .types
        .catalog
        .param_bounds
        .get(&base_symbol)?
        .iter()
        .find_map(|protocol| {
            module
                .types
                .catalog
                .associated_type_in_ref(protocol, &label)
                .map(|(_, assoc)| assoc)
        })
}

fn effect_symbol_at_offset(
    effects: &crate::node_kinds::func::EffectSet,
    byte_offset: u32,
) -> Option<Symbol> {
    for (name, span) in effects.names.iter().zip(effects.spans.iter()) {
        if effect_span_contains(*span, byte_offset) {
            return name.symbol().ok();
        }
    }
    None
}

fn effect_span_contains(span: crate::span::Span, byte_offset: u32) -> bool {
    span_contains(span, byte_offset) || (span.start > 0 && byte_offset == span.start - 1)
}

fn target_import_aliases(
    module: &AnalysisWorkspace,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    symbol: Symbol,
) -> FxHashSet<String> {
    use crate::node_kinds::decl::{DeclKind, ImportedSymbols};

    let mut aliases = FxHashSet::default();
    for node in &ast.roots {
        let crate::node::Node::Decl(decl) = node else {
            continue;
        };
        let DeclKind::Import(import) = &decl.kind else {
            continue;
        };
        let ImportedSymbols::Named(imported_symbols) = &import.symbols else {
            continue;
        };
        for imported in imported_symbols {
            if let Some(alias) = &imported.alias
                && symbol_exported_by_import(module, &ast.path, import, &imported.name)
                    == Some(symbol)
            {
                aliases.insert(alias.clone());
            }
        }
    }
    aliases
}

fn rename_spans_in_ast(
    module: &AnalysisWorkspace,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    symbol: Symbol,
) -> Vec<(u32, u32)> {
    let target_import_aliases = target_import_aliases(module, ast, symbol);
    let mut collector = RenameCollector {
        module,
        ast,
        target: symbol,
        target_import_aliases,
        spans: FxHashSet::default(),
    };

    for root in &ast.roots {
        root.drive(&mut collector);
    }

    let mut spans: Vec<(u32, u32)> = collector.spans.into_iter().collect();
    spans.sort_unstable();
    spans
}

#[derive(Visitor)]
#[visitor(
    Decl(enter),
    Expr(enter),
    Func(enter),
    FuncSignature(enter),
    GenericDecl(enter),
    Parameter(enter),
    Pattern(enter),
    RecordFieldPattern(enter),
    Stmt(enter),
    TypeAnnotation(enter)
)]
struct RenameCollector<'a> {
    module: &'a AnalysisWorkspace,
    ast: &'a crate::ast::AST<crate::ast::NameResolved>,
    target: Symbol,
    target_import_aliases: FxHashSet<String>,
    spans: FxHashSet<(u32, u32)>,
}

impl RenameCollector<'_> {
    fn push_span(&mut self, span: crate::span::Span) {
        self.spans.insert((span.start, span.end));
    }

    fn push_u32_span(&mut self, start: u32, end: u32) {
        self.spans.insert((start, end));
    }

    fn should_rename_visible_reference(&self, name: &crate::name::Name) -> bool {
        !self.target_import_aliases.contains(&name.name_str())
    }

    fn enter_decl(&mut self, decl: &crate::node_kinds::decl::Decl) {
        use crate::node_kinds::decl::DeclKind;

        match &decl.kind {
            DeclKind::Import(import) => self.enter_import_decl(import),
            DeclKind::Struct {
                name, name_span, ..
            }
            | DeclKind::Protocol {
                name, name_span, ..
            }
            | DeclKind::Extend {
                name, name_span, ..
            }
            | DeclKind::Enum {
                name, name_span, ..
            }
            | DeclKind::Property {
                name, name_span, ..
            }
            | DeclKind::Effect {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            DeclKind::TypeAlias(name, name_span, ..) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            DeclKind::EnumVariant {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            _ => {}
        }
    }

    fn enter_import_decl(&mut self, import: &crate::node_kinds::decl::Import) {
        use crate::node_kinds::decl::ImportedSymbols;

        let ImportedSymbols::Named(imported_symbols) = &import.symbols else {
            return;
        };

        for imported in imported_symbols {
            let symbol =
                symbol_exported_by_import(self.module, &self.ast.path, import, &imported.name);
            if symbol == Some(self.target) {
                self.push_span(imported.span);
            }
        }
    }

    fn enter_func(&mut self, func: &crate::node_kinds::func::Func) {
        if func.name.symbol().ok() == Some(self.target) {
            self.push_span(func.name_span);
        }
        self.push_matching_effect_spans(&func.effects);
    }

    fn enter_func_signature(&mut self, sig: &crate::node_kinds::func_signature::FuncSignature) {
        if sig.name.symbol().ok() == Some(self.target)
            && let Some(meta) = self.ast.meta.get(&sig.id)
            && let Some(tok) = meta.identifiers.first()
        {
            self.push_u32_span(tok.start, tok.end);
        }
        self.push_matching_effect_spans(&sig.effects);
    }

    fn enter_generic_decl(&mut self, generic: &crate::node_kinds::generic_decl::GenericDecl) {
        if generic.name.symbol().ok() == Some(self.target) {
            self.push_span(generic.name_span);
        }
    }

    fn enter_parameter(&mut self, param: &crate::node_kinds::parameter::Parameter) {
        if param.name.symbol().ok() == Some(self.target) {
            self.push_span(param.name_span);
        }
    }

    fn enter_pattern(&mut self, pattern: &crate::node_kinds::pattern::Pattern) {
        use crate::node_kinds::pattern::PatternKind;

        match &pattern.kind {
            PatternKind::Bind(name) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(pattern.span);
                }
            }
            PatternKind::Variant {
                variant_name_span, ..
            } => {
                if symbol_for_member_resolution(
                    self.module.types.member_resolutions.get(&pattern.id),
                ) == Some(self.target)
                {
                    self.push_span(*variant_name_span);
                }
            }
            _ => {}
        }
    }

    fn enter_record_field_pattern(
        &mut self,
        field: &crate::node_kinds::pattern::RecordFieldPattern,
    ) {
        use crate::node_kinds::pattern::RecordFieldPatternKind;

        match &field.kind {
            RecordFieldPatternKind::Bind(name) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(field.span);
                }
            }
            RecordFieldPatternKind::Equals {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            RecordFieldPatternKind::Rest => {}
        }
    }

    fn enter_type_annotation(&mut self, ty: &crate::node_kinds::type_annotation::TypeAnnotation) {
        use crate::node_kinds::type_annotation::TypeAnnotationKind;

        match &ty.kind {
            TypeAnnotationKind::Nominal {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target)
                    && self.should_rename_visible_reference(name)
                {
                    self.push_span(*name_span);
                }
            }
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_span,
                ..
            } => {
                if symbol_for_associated_type_member(self.module, base, member) == Some(self.target)
                {
                    self.push_span(*member_span);
                }
            }
            TypeAnnotationKind::Any {
                protocol,
                assoc_bindings,
            } => {
                for binding in assoc_bindings {
                    if symbol_for_any_assoc_binding(self.module, protocol, binding)
                        == Some(self.target)
                    {
                        self.push_span(binding.name_span);
                    }
                }
            }
            _ => {}
        }
    }

    fn enter_stmt(&mut self, stmt: &crate::node_kinds::stmt::Stmt) {
        use crate::node_kinds::stmt::StmtKind;

        let StmtKind::Handling {
            effect_name,
            effect_name_span,
            ..
        } = &stmt.kind
        else {
            return;
        };

        if effect_name.symbol().ok() == Some(self.target) {
            self.push_span(*effect_name_span);
        }
    }

    fn enter_expr(&mut self, expr: &crate::node_kinds::expr::Expr) {
        use crate::node_kinds::expr::ExprKind;

        match &expr.kind {
            ExprKind::Variable(name) | ExprKind::Constructor(name) => {
                if name.symbol().ok() == Some(self.target)
                    && self.should_rename_visible_reference(name)
                {
                    self.push_span(expr.span);
                }
            }
            ExprKind::Member(_, _, label_span) => {
                if symbol_for_member_resolution(self.module.types.member_resolutions.get(&expr.id))
                    == Some(self.target)
                {
                    self.push_span(*label_span);
                }
            }
            ExprKind::Call { callee, args, .. } => {
                if let Some(struct_info) = construction_callee_symbol(callee)
                    .and_then(|symbol| self.module.types.catalog.structs.get(&symbol))
                {
                    for arg in args {
                        if struct_info
                            .fields
                            .get(&arg.label.to_string())
                            .is_some_and(|(symbol, _)| *symbol == self.target)
                        {
                            self.push_span(arg.label_span);
                        }
                    }
                }
            }
            ExprKind::CallEffect {
                effect_name,
                effect_name_span,
                ..
            } => {
                if effect_name.symbol().ok() == Some(self.target) {
                    self.push_span(*effect_name_span);
                }
            }
            _ => {}
        }
    }

    fn push_matching_effect_spans(&mut self, effects: &crate::node_kinds::func::EffectSet) {
        for (name, span) in effects.names.iter().zip(effects.spans.iter()) {
            if name.symbol().ok() == Some(self.target) {
                self.push_span(*span);
            }
        }
    }
}
