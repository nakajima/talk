use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    node_id::NodeID,
    node_kinds::{block::Block, expr::Expr},
    parsing::span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum StmtKind {
    Expr(Expr),
    If(
        Expr,          /* condition */
        Block,         /* then block */
        Option<Block>, /* else block */
    ),
    Return(Option<Expr>),
    Break,
    Assignment(Expr /* LHS */, Expr /* RHS */),
    Loop(Option<Expr> /* condition */, Block /* body */),
    Continue(Option<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct Stmt {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: StmtKind,
    #[drive(skip)]
    pub span: Span,
}

impl Stmt {
    #[allow(clippy::panic)]
    pub fn as_expr(self) -> Expr {
        if let StmtKind::Expr(expr) = self.kind {
            expr
        } else {
            panic!("Called as_expr on non-expr statement");
        }
    }
}

impl_into_node!(Stmt);
