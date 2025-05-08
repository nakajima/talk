use crate::{token::Token, token_kind::TokenKind};

use super::func_expr::FuncExpr;

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
    Tuple(Vec<usize>),
    EmptyTuple,
    Block(Vec<usize>),
    Func(FuncExpr),
    Variable(&'static str),
}
