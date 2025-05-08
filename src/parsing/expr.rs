use crate::{token::Token, token_kind::TokenKind};

use super::{parse_tree::ParseTree, visitor::Visitor};

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
    Binary(usize, usize, TokenKind),
    Grouping(usize),
}
