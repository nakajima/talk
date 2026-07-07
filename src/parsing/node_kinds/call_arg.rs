use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, label::Label, node_id::NodeID, node_kinds::expr::Expr, parsing::span::Span,
};

/// A call-site ownership marker on an argument (ADR 0018): an escape
/// hatch/documentation for non-default ownership at the call.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArgMode {
    /// `borrow value` — require the parameter to borrow.
    Borrow,
    /// `mut value` — require exclusive access to the argument place.
    Mut,
    /// `consume value` — force a move; disables automatic cloning.
    Consume,
    /// `copy value` — force a copy/clone; disables last-use move selection.
    Copy,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct CallArg {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Label,
    #[drive(skip)]
    pub label_span: Span,
    pub value: Expr,
    #[drive(skip)]
    pub span: Span,
    #[drive(skip)]
    pub mode: Option<ArgMode>,
    #[drive(skip)]
    pub mode_span: Option<Span>,
}

impl_into_node!(CallArg);
