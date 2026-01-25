use async_lsp::lsp_types::{TextEdit, Url, WorkspaceEdit};
use derive_visitor::{Drive, Visitor};
use rustc_hash::FxHashSet;

use crate::analysis::{node_ids_at_offset, resolve_member_symbol, span_contains};
use crate::analysis::workspace::Workspace as AnalysisWorkspace;
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
    stmt::Stmt,
    type_annotation::TypeAnnotation,
};
use crate::token_kind::TokenKind;

use super::goto_definition::{
    goto_definition_symbol_from_decl, goto_definition_symbol_from_expr,
    goto_definition_symbol_from_stmt, goto_definition_symbol_from_type_annotation,
};
use super::server::{byte_span_to_range_utf16, document_id_for_uri, url_from_document_id};

fn is_valid_identifier(name: &str) -> bool {
    let mut lexer = Lexer::new(name);
    let Ok(token) = lexer.next() else {
        return false;
    };
    if !matches!(token.kind, TokenKind::Identifier(..)) {
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
        let spans = rename_spans_in_ast(ast, module.types.as_ref(), symbol);

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
            crate::node::Node::Expr(expr) => {
                goto_definition_symbol_from_expr(module.types.as_ref(), &expr, byte_offset)
            }
            crate::node::Node::Stmt(stmt) => {
                goto_definition_symbol_from_stmt(module.types.as_ref(), &stmt, byte_offset)
            }
            crate::node::Node::TypeAnnotation(ty) => {
                goto_definition_symbol_from_type_annotation(&ty, byte_offset)
            }
            crate::node::Node::Decl(decl) => goto_definition_symbol_from_decl(&decl, byte_offset),
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

fn rename_spans_in_ast(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    types: Option<&crate::types::types::Types>,
    symbol: Symbol,
) -> Vec<(u32, u32)> {
    let mut collector = RenameCollector {
        ast,
        types,
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
    Stmt(enter),
    TypeAnnotation(enter)
)]
struct RenameCollector<'a> {
    ast: &'a crate::ast::AST<crate::ast::NameResolved>,
    types: Option<&'a crate::types::types::Types>,
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
            DeclKind::TypeAlias(name, name_span, ..)
            | DeclKind::EnumVariant(name, name_span, ..) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            DeclKind::Effect {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            _ => {}
        }
    }

    fn enter_func(&mut self, func: &crate::node_kinds::func::Func) {
        if func.name.symbol().ok() == Some(self.target) {
            self.push_span(func.name_span);
        }

        // Check effect annotations in the function signature
        for (name, span) in func.effects.names.iter().zip(func.effects.spans.iter()) {
            if name.symbol().ok() == Some(self.target) {
                self.push_span(*span);
            }
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

        match &pattern.kind {
            PatternKind::Bind(name) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(pattern.span);
                }
            }
            PatternKind::Variant {
                enum_name,
                variant_name,
                variant_name_span,
                ..
            } => {
                // Check if the variant refers to our target symbol
                if let Some(variant_symbol) = self.lookup_variant_symbol(pattern, enum_name.as_ref(), variant_name) {
                    if variant_symbol == self.target {
                        self.push_span(*variant_name_span);
                    }
                }
            }
            _ => {}
        }
    }

    /// Look up the symbol for a variant pattern
    fn lookup_variant_symbol(
        &self,
        pattern: &crate::node_kinds::pattern::Pattern,
        enum_name: Option<&crate::name::Name>,
        variant_name: &str,
    ) -> Option<Symbol> {
        let types = self.types?;
        let label: crate::label::Label = variant_name.to_string().into();

        // First try: if enum_name is explicitly provided
        if let Some(enum_name) = enum_name {
            let enum_symbol = enum_name.symbol().ok()?;
            return types.catalog.variants.get(&enum_symbol)?.get(&label).copied();
        }

        // Second try: infer enum from the pattern's type
        if let Some(entry) = types.get(&pattern.id) {
            let ty = entry.as_mono_ty();
            if let crate::types::ty::Ty::Nominal { symbol, .. } = ty {
                return types.catalog.variants.get(symbol)?.get(&label).copied();
            }
        }

        // Third try: Find parent match expression and use scrutinee type
        for (node_id, meta) in self.ast.meta.iter() {
            if meta.start.start <= pattern.span.start && pattern.span.end <= meta.end.end {
                if let Some(node) = self.ast.find(*node_id) {
                    if let crate::node::Node::Stmt(stmt) = &node {
                        if let crate::node_kinds::stmt::StmtKind::Expr(expr) = &stmt.kind {
                            if let crate::node_kinds::expr::ExprKind::Match(scrutinee, _) = &expr.kind {
                                if let Some(entry) = types.get(&scrutinee.id) {
                                    let ty = entry.as_mono_ty();
                                    if let crate::types::ty::Ty::Nominal { symbol, .. } = ty {
                                        return types.catalog.variants.get(symbol)?.get(&label).copied();
                                    }
                                }
                            }
                        }
                    }
                    if let crate::node::Node::Expr(expr) = node {
                        if let crate::node_kinds::expr::ExprKind::Match(scrutinee, _) = &expr.kind {
                            if let Some(entry) = types.get(&scrutinee.id) {
                                let ty = entry.as_mono_ty();
                                if let crate::types::ty::Ty::Nominal { symbol, .. } = ty {
                                    return types.catalog.variants.get(symbol)?.get(&label).copied();
                                }
                            }
                        }
                    }
                }
            }
        }

        None
    }

    /// Look up the variant symbol from an expression's type (for shorthand .Variant access)
    fn lookup_variant_from_expr_type(
        &self,
        expr: &crate::node_kinds::expr::Expr,
        label: &crate::label::Label,
    ) -> Option<Symbol> {
        use crate::types::ty::Ty;

        let types = self.types?;

        // Get the expression's type
        if let Some(entry) = types.get(&expr.id) {
            let ty = entry.as_mono_ty();

            // For a variant constructor like .Some, the type is Func(params..., return_type, effects)
            // The return type contains the enum's Nominal type
            let enum_symbol = match ty {
                Ty::Nominal { symbol, .. } => Some(symbol),
                Ty::Func(_, ret, _) => {
                    // The return type should be the Nominal enum type
                    if let Ty::Nominal { symbol, .. } = ret.as_ref() {
                        Some(symbol)
                    } else {
                        None
                    }
                }
                _ => None,
            };

            if let Some(symbol) = enum_symbol {
                return types.catalog.variants.get(symbol)?.get(label).copied();
            }
        }

        None
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

        let TypeAnnotationKind::Nominal {
            name, name_span, ..
        } = &ty.kind
        else {
            return;
        };

        if name.symbol().ok() == Some(self.target) {
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
            ExprKind::Member(receiver, label, name_span) => {
                if let Some(receiver) = receiver.as_ref() {
                    let member_sym = resolve_member_symbol(self.types, receiver, label);
                    if member_sym == Some(self.target) {
                        self.push_span(*name_span);
                    }
                } else {
                    // No receiver - this might be a shorthand variant access like .Some
                    // Look up the variant from the expression's type
                    if let Some(variant_sym) = self.lookup_variant_from_expr_type(expr, label) {
                        if variant_sym == self.target {
                            self.push_span(*name_span);
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

    fn enter_stmt(&mut self, stmt: &crate::node_kinds::stmt::Stmt) {
        use crate::node_kinds::stmt::StmtKind;

        if let StmtKind::Handling {
            effect_name,
            effect_name_span,
            ..
        } = &stmt.kind
        {
            if effect_name.symbol().ok() == Some(self.target) {
                self.push_span(*effect_name_span);
            }
        }
    }
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
