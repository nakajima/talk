use crate::{token::Token, token_kind::TokenKind};

use super::parser::NodeID;

pub type VarDepth = u32;

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub id: NodeID,
    pub start: Token,
    pub end: Token,
    pub kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    LiteralInt(&'static str),
    LiteralFloat(&'static str),
    Unary(TokenKind, NodeID),
    Binary(NodeID, TokenKind, NodeID),
    Tuple(Vec<NodeID>),
    EmptyTuple,
    Block(Vec<NodeID>),
    Func(
        Option<Token>,
        NodeID, /* params tuple */
        NodeID, /* body */
    ),
    Variable(&'static str),
    ResolvedVariable(VarDepth),
}
