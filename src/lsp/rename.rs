use async_lsp::lsp_types::{TextEdit, Url, WorkspaceEdit};
use derive_visitor::{Drive, Visitor};
use rustc_hash::FxHashSet;

use crate::analysis::workspace::Workspace as AnalysisWorkspace;
use crate::analysis::{node_ids_at_offset, span_contains};
use crate::compiling::module::ModuleId;
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

fn is_symbol_renamable(symbol: Symbol) -> bool {
    use crate::name_resolution::symbol::{
        AssociatedTypeId, EnumId, GlobalId, InitializerId, InstanceMethodId, MethodRequirementId,
        PropertyId, ProtocolId, StaticMethodId, StructId, TypeAliasId, VariantId,
    };

    match symbol {
        Symbol::Builtin(..) | Symbol::Main | Symbol::Library | Symbol::Synthesized(..) => false,

        Symbol::Struct(StructId { module_id, .. })
        | Symbol::Enum(EnumId { module_id, .. })
        | Symbol::TypeAlias(TypeAliasId { module_id, .. })
        | Symbol::Global(GlobalId { module_id, .. })
        | Symbol::Property(PropertyId { module_id, .. })
        | Symbol::InstanceMethod(InstanceMethodId { module_id, .. })
        | Symbol::Initializer(InitializerId { module_id, .. })
        | Symbol::StaticMethod(StaticMethodId { module_id, .. })
        | Symbol::Variant(VariantId { module_id, .. })
        | Symbol::Protocol(ProtocolId { module_id, .. })
        | Symbol::AssociatedType(AssociatedTypeId { module_id, .. })
        | Symbol::Effect(EffectId { module_id, .. })
        | Symbol::MethodRequirement(MethodRequirementId { module_id, .. }) => {
            module_id == ModuleId::Current
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
    if !is_symbol_renamable(symbol) {
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
    let candidate_ids = node_ids_at_offset(ast, byte_offset);

    for node_id in candidate_ids {
        let Some(node) = ast.find(node_id) else {
            continue;
        };

        let symbol = match node {
            crate::node::Node::Expr(expr) => goto_definition_symbol_from_expr(&expr, byte_offset),
            crate::node::Node::Stmt(stmt) => goto_definition_symbol_from_stmt(&stmt, byte_offset),
            crate::node::Node::TypeAnnotation(ty) => {
                goto_definition_symbol_from_type_annotation(&ty, byte_offset)
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
                    None
                }
            }
            crate::node::Node::FuncSignature(sig) => {
                let meta = ast.meta.get(&sig.id)?;
                let (start, end) = meta.identifiers.first().map(|t| (t.start, t.end))?;
                if start <= byte_offset && byte_offset <= end {
                    sig.name.symbol().ok()
                } else {
                    None
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

fn goto_definition_symbol_from_expr(
    expr: &crate::node_kinds::expr::Expr,
    _byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::expr::ExprKind;

    match &expr.kind {
        ExprKind::Variable(name) | ExprKind::Constructor(name) => name.symbol().ok(),
        _ => None,
    }
}

fn goto_definition_symbol_from_stmt(
    stmt: &crate::node_kinds::stmt::Stmt,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::stmt::StmtKind;

    match &stmt.kind {
        StmtKind::Expr(expr) => goto_definition_symbol_from_expr(expr, byte_offset),
        StmtKind::Return(Some(expr)) => goto_definition_symbol_from_expr(expr, byte_offset),
        StmtKind::If(cond, ..) => goto_definition_symbol_from_expr(cond, byte_offset),
        StmtKind::Loop(Some(cond), ..) => goto_definition_symbol_from_expr(cond, byte_offset),
        StmtKind::Assignment(lhs, rhs) => goto_definition_symbol_from_expr(lhs, byte_offset)
            .or_else(|| goto_definition_symbol_from_expr(rhs, byte_offset)),
        _ => None,
    }
}

fn goto_definition_symbol_from_type_annotation(
    ty: &crate::node_kinds::type_annotation::TypeAnnotation,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    match &ty.kind {
        TypeAnnotationKind::Borrow { inner, .. } => {
            goto_definition_symbol_from_type_annotation(inner, byte_offset)
        }
        TypeAnnotationKind::Nominal {
            name, name_span, ..
        } => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        TypeAnnotationKind::Any {
            protocol,
            assoc_bindings,
        } => goto_definition_symbol_from_type_annotation(protocol, byte_offset).or_else(|| {
            assoc_bindings.iter().find_map(|binding| {
                goto_definition_symbol_from_type_annotation(&binding.value, byte_offset)
            })
        }),
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

fn rename_spans_in_ast(
    module: &AnalysisWorkspace,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    symbol: Symbol,
) -> Vec<(u32, u32)> {
    let mut collector = RenameCollector {
        module,
        ast,
        target: symbol,
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
    TypeAnnotation(enter)
)]
struct RenameCollector<'a> {
    module: &'a AnalysisWorkspace,
    ast: &'a crate::ast::AST<crate::ast::NameResolved>,
    target: Symbol,
    spans: FxHashSet<(u32, u32)>,
}

impl RenameCollector<'_> {
    fn push_span(&mut self, span: crate::span::Span) {
        self.spans.insert((span.start, span.end));
    }

    fn push_u32_span(&mut self, start: u32, end: u32) {
        self.spans.insert((start, end));
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
    }

    fn enter_func_signature(&mut self, sig: &crate::node_kinds::func_signature::FuncSignature) {
        if sig.name.symbol().ok() != Some(self.target) {
            return;
        }

        let Some(meta) = self.ast.meta.get(&sig.id) else {
            return;
        };
        let Some(tok) = meta.identifiers.first() else {
            return;
        };
        self.push_u32_span(tok.start, tok.end);
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

        let PatternKind::Bind(name) = &pattern.kind else {
            return;
        };

        if name.symbol().ok() == Some(self.target) {
            self.push_span(pattern.span);
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

        if let TypeAnnotationKind::Nominal {
            name, name_span, ..
        } = &ty.kind
            && name.symbol().ok() == Some(self.target)
        {
            self.push_span(*name_span);
        }
    }

    fn enter_expr(&mut self, expr: &crate::node_kinds::expr::Expr) {
        use crate::node_kinds::expr::ExprKind;

        match &expr.kind {
            ExprKind::Variable(name) | ExprKind::Constructor(name) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(expr.span);
                }
            }
            _ => {}
        }
    }
}
