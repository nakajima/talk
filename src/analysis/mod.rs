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
    Effect,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompletionItem {
    pub label: String,
    pub kind: Option<CompletionItemKind>,
    pub detail: Option<String>,
}

pub use workspace::Workspace;

pub(crate) fn span_contains(span: crate::span::Span, byte_offset: u32) -> bool {
    span.start <= byte_offset && byte_offset <= span.end
}
