use crate::{token::Token, token_kind::TokenKind};

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub id: usize,
    pub start: Token,
    pub end: Token,
    pub kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    LiteralInt(&'static str),
    LiteralFloat(&'static str),
    Unary(TokenKind, usize),
    Binary(usize, TokenKind, usize),
    Grouping(usize),
    Tuple(Vec<usize>),
    EmptyTuple,
    Variable(&'static str),
}
