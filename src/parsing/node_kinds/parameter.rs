use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, name::Name, node_id::NodeID, node_kinds::type_annotation::TypeAnnotation,
    parsing::span::Span,
};

/// A parameter's ownership mode (ADR 0018). `None` on `Parameter.mode`
/// means the declaration was unadorned; what that defaults to is decided
/// during desugaring (`Borrow` ordinarily, `Consume` in `init` position).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ParamMode {
    /// `borrow x: T` — shared borrow (the explicit spelling of the default).
    Borrow,
    /// `mut x: T` — exclusive/inout borrow.
    Mut,
    /// `consume x: T` — the callee takes ownership.
    Consume,
    /// `consume mut x: T` — owned and locally mutable.
    ConsumeMut,
}

impl ParamMode {
    /// The mode's source spelling, for diagnostics.
    pub fn keyword(self) -> &'static str {
        match self {
            Self::Borrow => "borrow",
            Self::Mut => "mut",
            Self::Consume => "consume",
            Self::ConsumeMut => "consume mut",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Parameter {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    #[drive(skip)]
    pub name_span: Span,
    pub type_annotation: Option<TypeAnnotation>,
    #[drive(skip)]
    pub span: Span,
    #[drive(skip)]
    pub mode: Option<ParamMode>,
    #[drive(skip)]
    pub mode_span: Option<Span>,
}

impl_into_node!(Parameter);

impl Parameter {
    pub fn new(
        id: NodeID,
        name: Name,
        name_span: Span,
        type_annotation: Option<TypeAnnotation>,
        span: Span,
    ) -> Self {
        Self {
            id,
            name,
            name_span,
            type_annotation,
            span,
            mode: None,
            mode_span: None,
        }
    }
}
