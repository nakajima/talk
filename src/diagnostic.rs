use crate::{
    SourceFile,
    lexer::LexerError,
    lowering::lowerer::IRError,
    name_resolver::NameResolverError,
    parser::{ExprID, ParserError},
    token::Token,
    type_checker::TypeError,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Position {
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DiagnosticKind {
    Lexer(Position, LexerError),
    Parse(Token, ParserError),
    Resolve(ExprID, NameResolverError),
    Typing(ExprID, TypeError),
    Lowering(ExprID, IRError),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    kind: DiagnosticKind,
}

impl Diagnostic {
    pub fn lexer(position: Position, err: LexerError) -> Diagnostic {
        Self {
            kind: DiagnosticKind::Lexer(position, err),
        }
    }

    pub fn parser(token: Token, err: ParserError) -> Diagnostic {
        Self {
            kind: DiagnosticKind::Parse(token, err),
        }
    }

    pub fn resolve(expr_id: ExprID, err: NameResolverError) -> Diagnostic {
        Self {
            kind: DiagnosticKind::Resolve(expr_id, err),
        }
    }

    pub fn typing(expr_id: ExprID, err: TypeError) -> Diagnostic {
        Self {
            kind: DiagnosticKind::Typing(expr_id, err),
        }
    }

    pub fn lowering(expr_id: ExprID, err: IRError) -> Diagnostic {
        Self {
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
            DiagnosticKind::Typing(_, err) => *err != TypeError::Handled,
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
                let expr = source_file.meta.get(*expr_id as usize).unwrap();
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
                let expr = source_file.meta.get(*expr_id as usize).unwrap();

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
                let expr = source_file.meta.get(*expr_id as usize).unwrap();

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
