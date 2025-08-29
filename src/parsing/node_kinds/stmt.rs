use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    node::Node,
    node_id::NodeID,
    node_kinds::{block::Block, expr::Expr, pattern::Pattern},
    parsing::span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum StmtKind {
    Expr(Expr),
    If(Expr /* condition */, Block /* then block */),
    Return(Option<Expr>),
    Break,
    LetAssignment(Pattern /* LHS */, Expr /* RHS */),
    Assignment(Expr /* LHS */, Expr /* RHS */),
    Loop(Option<Expr> /* condition */, Block /* body */),
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct Stmt {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: StmtKind,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(Stmt);
