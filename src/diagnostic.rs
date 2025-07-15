use std::{hash::Hash, path::PathBuf};

use crate::{
    SourceFile, expr_id::ExprID, lexer::LexerError, lowering::ir_error::IRError,
    name_resolver::NameResolverError, parser::ParserError, token::Token, type_checker::TypeError,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Position {
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiagnosticKind {
    Lexer(Position, LexerError),
    Parse(Token, ParserError),
    Resolve(ExprID, NameResolverError),
    Typing(ExprID, TypeError),
    Lowering(ExprID, IRError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub kind: DiagnosticKind,
    pub path: PathBuf,
}

impl Hash for Diagnostic {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        format!("{self:?}").hash(state)
    }
}

impl Diagnostic {
    pub fn lexer(path: PathBuf, position: Position, err: LexerError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Lexer(position, err),
        }
    }

    pub fn parser(path: PathBuf, token: Token, err: ParserError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Parse(token, err),
        }
    }

    pub fn resolve(path: PathBuf, expr_id: ExprID, err: NameResolverError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Resolve(expr_id, err),
        }
    }

    pub fn typing(path: PathBuf, expr_id: ExprID, err: TypeError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Typing(expr_id, err),
        }
    }

    pub fn lowering(path: PathBuf, expr_id: ExprID, err: IRError) -> Diagnostic {
        Self {
            path,
            kind: DiagnosticKind::Lowering(expr_id, err),
        }
    }

    pub fn message(&self) -> String {
        match &self.kind {
            DiagnosticKind::Lexer(_, e) => e.message(),
            DiagnosticKind::Parse(_, e) => e.message(),
            DiagnosticKind::Resolve(_, e) => e.message(),
            DiagnosticKind::Typing(_, e) => e.message(),
            DiagnosticKind::Lowering(_, e) => e.message(),
        }
    }

    pub fn is_unhandled(&self) -> bool {
        match &self.kind {
            DiagnosticKind::Typing(_, err) => {
                *err != TypeError::Handled && !matches!(err, TypeError::Defer(_))
            }
            _ => true,
        }
    }

    pub fn range<S: crate::source_file::Phase>(
        &self,
        source_file: &SourceFile<S>,
    ) -> (Position, Position) {
        match &self.kind {
            DiagnosticKind::Lexer(position, _lexer_error) => (position.clone(), position.clone()),
            DiagnosticKind::Parse(token, _parser_error) => (
                Position {
                    line: token.line,
                    col: token.col,
                },
                Position {
                    line: token.line,
                    col: token.col,
                },
            ),
            DiagnosticKind::Resolve(expr_id, _name_resolver_error) => {
                let meta = source_file.meta.borrow();
                let Some(expr) = meta.get(expr_id) else {
                    return (Position { line: 0, col: 0 }, Position { line: 0, col: 0 });
                };

                (
                    Position {
                        line: expr.start.line,
                        col: expr.start.col,
                    },
                    Position {
                        line: expr.end.line,
                        col: expr.end.col,
                    },
                )
            }
            DiagnosticKind::Typing(expr_id, _type_error) => {
                let meta = source_file.meta.borrow();
                let Some(expr) = meta.get(expr_id) else {
                    return (Position { line: 0, col: 0 }, Position { line: 0, col: 0 });
                };

                (
                    Position {
                        line: expr.start.line,
                        col: expr.start.col,
                    },
                    Position {
                        line: expr.end.line,
                        col: expr.end.col,
                    },
                )
            }
            DiagnosticKind::Lowering(expr_id, _type_error) => {
                let meta = source_file.meta.borrow();
                let Some(expr) = meta.get(expr_id) else {
                    return (Position { line: 0, col: 0 }, Position { line: 0, col: 0 });
                };

                (
                    Position {
                        line: expr.start.line,
                        col: expr.start.col,
                    },
                    Position {
                        line: expr.end.line,
                        col: expr.end.col,
                    },
                )
            }
        }
    }
}
