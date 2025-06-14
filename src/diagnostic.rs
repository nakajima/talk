use crate::{
    lexer::LexerError,
    name_resolver::NameResolverError,
    parser::{ExprID, ParserError},
    token::Token,
    type_checker::TypeError,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Position {
    line: u32,
    col: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DiagnosticKind {
    Lexer(Position, LexerError),
    Parse(Token, ParserError),
    Resolve(ExprID, NameResolverError),
    Typing(ExprID, TypeError),
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
}
