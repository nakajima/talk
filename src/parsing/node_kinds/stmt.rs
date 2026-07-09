use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    name::Name,
    node_id::NodeID,
    node_kinds::{block::Block, call_arg::ArgMode, expr::Expr, pattern::Pattern},
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
    Assignment(Box<Expr> /* LHS */, Box<Expr> /* RHS */),
    Loop(Option<Expr> /* condition */, Block /* body */),
    For {
        iterable: Box<Expr>,
        /// ADR 0021: an ownership marker on the iterable selects the
        /// iteration mode (`consume xs` -> into_iter, `mut xs` -> iter_mut).
        #[drive(skip)]
        source_mode: Option<ArgMode>,
        pattern: Pattern,
        body: Block,
        /// The hidden source/iterator bindings the loop's elaboration
        /// scopes to it — named here so resolution declares their symbols
        /// with the loop's scope.
        #[drive(skip)]
        hidden_source: Name,
        #[drive(skip)]
        hidden_iter: Name,
    },
    Continue(Option<Expr>),
    Handling {
        #[drive(skip)]
        effect_name: Name,
        #[drive(skip)]
        effect_name_span: Span,
        body: Block,
    },
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
