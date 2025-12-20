pub mod completion;
pub mod hover;
pub mod workspace;

pub type DocumentId = String;

#[derive(Clone, Debug)]
pub struct DocumentInput {
    pub id: DocumentId,
    pub path: String,
    pub version: i32,
    pub text: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TextRange {
    pub start: u32,
    pub end: u32,
}

impl TextRange {
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    Error,
    Warning,
    Info,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub range: TextRange,
    pub severity: DiagnosticSeverity,
    pub message: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hover {
    pub contents: String,
    pub range: Option<TextRange>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompletionItemKind {
    Struct,
    Enum,
    Interface,
    Class,
    TypeParameter,
    Variable,
    Field,
    Method,
    Constructor,
    EnumMember,
    Keyword,
    Module,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompletionItem {
    pub label: String,
    pub kind: Option<CompletionItemKind>,
    pub detail: Option<String>,
}

pub use workspace::Workspace;

pub(crate) fn node_ids_at_offset(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    byte_offset: u32,
) -> Vec<crate::node_id::NodeID> {
    let mut candidates: Vec<(crate::node_id::NodeID, u32)> = ast
        .meta
        .iter()
        .filter_map(|(id, meta)| {
            let start = meta.start.start;
            let end = meta.end.end;
            if start <= byte_offset && byte_offset <= end {
                Some((*id, end.saturating_sub(start)))
            } else {
                None
            }
        })
        .collect();

    candidates.sort_by_key(|(_, len)| *len);
    candidates.into_iter().map(|(id, _)| id).collect()
}

pub(crate) fn span_contains(span: crate::span::Span, byte_offset: u32) -> bool {
    span.start <= byte_offset && byte_offset <= span.end
}

pub(crate) fn resolve_member_symbol(
    types: Option<&crate::types::type_session::Types>,
    receiver: &crate::node_kinds::expr::Expr,
    label: &crate::label::Label,
) -> Option<crate::name_resolution::symbol::Symbol> {
    use crate::node_kinds::expr::ExprKind;
    use crate::types::ty::Ty;

    if let ExprKind::Constructor(name) = &receiver.kind {
        let receiver_symbol = name.symbol().ok()?;
        let types = types?;
        return types.catalog.lookup_static_member(&receiver_symbol, label);
    }

    let types = types?;
    let entry = types.get(&receiver.id)?;
    let ty = entry.as_mono_ty();

    match ty {
        Ty::Nominal { symbol, .. } => types.catalog.lookup_member(symbol, label).map(|m| m.0),
        _ => None,
    }
}
