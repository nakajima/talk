use crate::{token::Token, token_kind::TokenKind};

use super::parser::NodeID;

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
    Unary(TokenKind, NodeID),
    Binary(NodeID, TokenKind, NodeID),
    Tuple(Vec<NodeID>),
    Block(Vec<NodeID>),
    Func(
        Option<Token>,
        Vec<NodeID>, /* params tuple */
        NodeID, /* body */
    ),
    Parameter(&'static str),
    Variable(&'static str),
    ResolvedVariable(VarDepth),
    Assignment(NodeID /* LHS */, NodeID /* RHS */),
    Let(&'static str),
}

