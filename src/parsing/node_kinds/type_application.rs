use derive_visitor::{Drive, DriveMut};

use crate::{
    name::Name,
    name_resolution::name_resolver::NameResolverError,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::generic_arg::GenericArg,
    parsing::span::Span,
};

/// A nominal application: a name applied to generic arguments. This is the
/// extension-head shape (ADR 0036): the grammar admits a name plus ordinary
/// `GenericArg`s and nothing else — sugar (`[T]`, `T?`) and non-nominal
/// forms are unrepresentable, so no consumer re-derives what was typed.
#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct TypeApplication {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub span: Span,
    #[drive(skip)]
    pub name: Name,
    #[drive(skip)]
    pub name_span: Span,
    pub args: Vec<GenericArg>,
}

impl TypeApplication {
    pub fn symbol(&self) -> Result<Symbol, NameResolverError> {
        self.name.symbol()
    }
}
