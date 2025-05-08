use crate::{token::Token, token_kind::TokenKind};

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Expr {
    pub id: usize,
    pub start: Token,
    pub end: Token,
    pub kind: ExprKind,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ExprKind {
    LiteralInt(&'static str),
    LiteralFloat(&'static str),
    Unary(usize, TokenKind),
    Binary(usize, usize, TokenKind),
    Grouping(usize),
    Variable(&'static str),
}
