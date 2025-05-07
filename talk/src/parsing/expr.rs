use crate::tokens::Token;

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Expr<'a> {
    pub id: usize,
    pub start: Token<'a>,
    pub end: Token<'a>,
    pub kind: ExprKind
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ExprKind {
    LiteralInt,
    LiteralFloat,
    Binary(usize, usize)
}
