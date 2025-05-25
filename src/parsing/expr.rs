use crate::{symbol_table::SymbolID, token::Token, token_kind::TokenKind};

use super::parser::ExprID;

pub type VarDepth = u32;

#[derive(Clone, Debug, PartialEq)]
pub struct ExprMeta {
    pub start: Token,
    pub end: Token,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FuncName {
    Main,
    Token(&'static str),
    Resolved(SymbolID),
}

impl FuncName {
    pub fn replace(&mut self, func_name: FuncName) {
        *self = func_name
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    LiteralInt(&'static str),
    LiteralFloat(&'static str),
    LiteralTrue,
    LiteralFalse,
    Unary(TokenKind, ExprID),
    Binary(ExprID, TokenKind, ExprID),
    Tuple(Vec<ExprID>),
    Block(Vec<ExprID>),
    Call(ExprID, Vec<ExprID>),

    // A type annotation
    TypeRepr(&'static str),

    // Function stuff
    Func(
        Option<FuncName>,
        Vec<ExprID>,    /* params tuple */
        ExprID,         /* body */
        Option<ExprID>, /* return type */
    ),
    Parameter(
        &'static str,   /* name */
        Option<ExprID>, /* TypeRepr */
    ),

    // Variables
    Let(&'static str, Option<ExprID>),
    Assignment(ExprID /* LHS */, ExprID /* RHS */),
    Variable(&'static str),

    // For name resolution
    ResolvedVariable(SymbolID, Option<ExprID>),
    ResolvedLet(SymbolID, Option<ExprID> /* RHS */),

    // Control flow
    If(
        ExprID,         /* condition */
        ExprID,         /* condition block */
        Option<ExprID>, /* else block */
    ),

    Loop(Option<ExprID> /* condition */, ExprID /* body */),
}
