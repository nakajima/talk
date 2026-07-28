use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, label::Label, node_id::NodeID, node_kinds::expr::Expr, parsing::span::Span,
};

/// A call-site ownership marker on an argument (ADR 0018): an escape
/// hatch/documentation for non-default ownership at the call.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
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

/// Where a call argument came from (ADR 0041). Semantic analysis applies
/// the trailing-block label exception by origin — never by inspecting a
/// synthesized function name or span — and compiler-generated sugar is not
/// a source label occurrence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize)]
pub enum CallArgOrigin {
    /// Written inside the call's parentheses.
    #[default]
    Written,
    /// Desugared from a trailing block; its label is omitted by syntax.
    TrailingBlock,
    /// The leading argument of a paren-less string call (`say "hello"`);
    /// its label is omitted by syntax.
    BareString,
    /// Compiler-generated sugar (operators, subscripts, ranges, macros).
    Synthesized,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct CallArg {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Label,
    #[drive(skip)]
    pub label_span: Span,
    #[drive(skip)]
    pub origin: CallArgOrigin,
    pub value: Expr,
    #[drive(skip)]
    pub span: Span,
    #[drive(skip)]
    pub mode: Option<ArgMode>,
    #[drive(skip)]
    pub mode_span: Option<Span>,
}

impl_into_node!(CallArg);
