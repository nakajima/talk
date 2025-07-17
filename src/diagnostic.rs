use std::{hash::Hash, path::PathBuf};

use miette::{NamedSource, SourceSpan};

use crate::{
    ExprMetaStorage, lexer::LexerError, lowering::ir_error::IRError,
    name_resolver::NameResolverError, parser::ParserError, type_checker::TypeError,
};

#[derive(Debug, Clone, PartialEq, Eq, miette::Diagnostic)]
#[diagnostic(code(Talk::Diagnostic))]
pub struct ExpandedDiagnostic {
    kind: DiagnosticKind,
    message: String,

    // The `Source` that miette will use.
    #[source_code]
    src: NamedSource<String>,

    // This will underline/mark the specific code inside the larger
    // snippet context.
    #[label = "Error here"]
    err_span: SourceSpan,

    #[related]
    others: Vec<ExpandedDiagnostic>,
}

impl std::fmt::Display for ExpandedDiagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for ExpandedDiagnostic {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }

    fn description(&self) -> &str {
        "description() is deprecated; use Display"
    }

    fn cause(&self) -> Option<&dyn std::error::Error> {
        self.source()
    }

    fn provide<'a>(&'a self, _request: &mut std::error::Request<'a>) {}
}

use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Position {
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiagnosticKind {
    Lexer(LexerError),
    Parse(ParserError),
    Resolve(NameResolverError),
    Typing(TypeError),
    Lowering(IRError),
}

pub type ErrorSpan = (usize, usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub kind: DiagnosticKind,
    pub path: PathBuf,
    pub span: ErrorSpan,
}

impl Hash for Diagnostic {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        format!("{self:?}").hash(state)
    }
}

impl Diagnostic {
    pub fn lexer(path: PathBuf, span: ErrorSpan, err: LexerError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Lexer(err),
            span,
        }
    }

    pub fn parser(path: PathBuf, span: ErrorSpan, err: ParserError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Parse(err),
            span,
        }
    }

    pub fn resolve(path: PathBuf, span: ErrorSpan, err: NameResolverError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Resolve(err),
            span,
        }
    }

    pub fn typing(path: PathBuf, span: ErrorSpan, err: TypeError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Typing(err),
            span,
        }
    }

    pub fn lowering(path: PathBuf, span: ErrorSpan, err: IRError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Lowering(err),
            span,
        }
    }

    pub fn message(&self) -> String {
        match &self.kind {
            DiagnosticKind::Lexer(e) => e.message(),
            DiagnosticKind::Parse(e) => e.message(),
            DiagnosticKind::Resolve(e) => e.message(),
            DiagnosticKind::Typing(e) => e.message(),
            DiagnosticKind::Lowering(e) => e.message(),
        }
    }

    pub fn is_unhandled(&self) -> bool {
        match &self.kind {
            DiagnosticKind::Typing(err) => {
                *err != TypeError::Handled && !matches!(err, TypeError::Defer(_))
            }
            _ => true,
        }
    }

    pub fn expand(&self, _meta: &ExprMetaStorage, source: &str) -> ExpandedDiagnostic {
        ExpandedDiagnostic {
            kind: self.kind.clone(),
            message: self.message(),
            src: NamedSource::new(self.path.to_str().unwrap_or("-"), source.to_string()),
            err_span: self.span.into(),
            others: vec![],
        }
    }
}
