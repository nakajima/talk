use std::{hash::Hash, path::PathBuf};

use miette::{NamedSource, SourceOffset, SourceSpan};

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
    // // You can add as many labels as you want.
    // // They'll be rendered sequentially.
    // #[label("This is bad")]
    // snip2: (usize, usize), // `(usize, usize)` is `Into<SourceSpan>`!

    // // Snippets can be optional, by using Option:
    // #[label("some text")]
    // snip3: Option<SourceSpan>,

    // // with or without label text
    // #[label]
    // snip4: Option<SourceSpan>,
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

    fn provide<'a>(&'a self, request: &mut std::error::Request<'a>) {}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    pub fn expand(&self, meta: &ExprMetaStorage, source: &str) -> ExpandedDiagnostic {
        let others = if let DiagnosticKind::Typing(TypeError::Mismatch(_, _, related)) = &self.kind
        {
            related
                .iter()
                .map(|id| {
                    Diagnostic::typing(
                        self.path.clone(),
                        meta.get(id).map(|m| m.span()).unwrap_or_default(),
                        TypeError::Unknown("Related".into()),
                    )
                    .expand(meta, source)
                })
                .collect()
        } else {
            vec![]
        };

        ExpandedDiagnostic {
            kind: self.kind.clone(),
            message: self.message(),
            src: NamedSource::new(self.path.to_str().unwrap_or("-"), source.to_string()),
            err_span: self.span.into(),
            others,
        }
    }

    // pub fn range<S: crate::source_file::Phase>(
    //     &self,
    //     source_file: &SourceFile<S>,
    // ) -> (Position, Position) {
    //     match &self.kind {
    //         DiagnosticKind::Lexer(_lexer_error) => (position.clone(), position.clone()),
    //         DiagnosticKind::Parse(_parser_error) => (
    //             Position {
    //                 line: token.line,
    //                 col: token.col,
    //             },
    //             Position {
    //                 line: token.line,
    //                 col: token.col,
    //             },
    //         ),
    //         DiagnosticKind::Resolve(expr_id, _name_resolver_error) => {
    //             let meta = source_file.meta.borrow();
    //             let Some(expr) = meta.get(expr_id) else {
    //                 return (Position { line: 0, col: 0 }, Position { line: 0, col: 0 });
    //             };

    //             (
    //                 Position {
    //                     line: expr.start.line,
    //                     col: expr.start.col,
    //                 },
    //                 Position {
    //                     line: expr.end.line,
    //                     col: expr.end.col,
    //                 },
    //             )
    //         }
    //         DiagnosticKind::Typing(expr_id, _type_error) => {
    //             let meta = source_file.meta.borrow();
    //             let Some(expr) = meta.get(expr_id) else {
    //                 return (Position { line: 0, col: 0 }, Position { line: 0, col: 0 });
    //             };

    //             (
    //                 Position {
    //                     line: expr.start.line,
    //                     col: expr.start.col,
    //                 },
    //                 Position {
    //                     line: expr.end.line,
    //                     col: expr.end.col,
    //                 },
    //             )
    //         }
    //         DiagnosticKind::Lowering(expr_id, _type_error) => {
    //             let meta = source_file.meta.borrow();
    //             let Some(expr) = meta.get(expr_id) else {
    //                 return (Position { line: 0, col: 0 }, Position { line: 0, col: 0 });
    //             };

    //             (
    //                 Position {
    //                     line: expr.start.line,
    //                     col: expr.start.col,
    //                 },
    //                 Position {
    //                     line: expr.end.line,
    //                     col: expr.end.col,
    //                 },
    //             )
    //         }
    //     }
    // }
}
