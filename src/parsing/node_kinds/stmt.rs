use derive_visitor::{Drive, DriveMut};

use crate::{
    node::Node,
    node_id::NodeID,
    node_kinds::{block::Block, expr::Expr},
};

#[derive(Clone, Debug, PartialEq, Eq, DriveMut, Drive)]
pub enum StmtKind {
    Expr(Expr),
    If(Expr /* condition */, Block /* then block */),
    Return(Option<Expr>),
    Break,
    Assignment(Expr /* LHS */, Expr /* RHS */),
    Loop(Option<Expr> /* condition */, Block /* body */),
}

#[derive(Clone, Debug, PartialEq, Eq, DriveMut, Drive)]
pub struct Stmt {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: StmtKind,
}

impl From<Stmt> for Node {
    fn from(val: Stmt) -> Self {
        Node::Stmt(val)
    }
}
