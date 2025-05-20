use crate::{token::Token, token_kind::TokenKind};

use super::parser::ExprID;

pub type VarDepth = u32;

#[derive(Clone, Debug, PartialEq)]
pub struct ExprMeta {
    pub start: Token,
    pub end: Token,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    LiteralInt(&'static str),
    LiteralFloat(&'static str),
    Unary(TokenKind, ExprID),
    Binary(ExprID, TokenKind, ExprID),
    Tuple(Vec<ExprID>),
    Block(Vec<ExprID>),
    Call(ExprID, Vec<ExprID>),
    TypeRepr(&'static str),
    Func(
        Option<Token>,
        Vec<ExprID>,    /* params tuple */
        ExprID,         /* body */
        Option<ExprID>, /* return type */
    ),
    Parameter(
        &'static str,   /* name */
        Option<ExprID>, /* TypeRepr */
    ),
    Variable(&'static str),
    ResolvedVariable(VarDepth, Option<ExprID>),
    Assignment(ExprID /* LHS */, ExprID /* RHS */),
    Let(&'static str),
}
