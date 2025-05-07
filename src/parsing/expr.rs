use crate::tokens::Token;

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
    Binary(usize, usize, Token),
    Grouping(usize),
}
