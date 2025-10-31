use indexmap::IndexMap;

use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{members::Members, type_catalog::ConformanceStub},
};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NominalKind {
    Struct,
    Enum,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Nominal<T> {
    pub name: Name,
    pub ty: T,
    pub node_id: NodeID,
    pub span: Span,
    pub kind: NominalKind,
    pub conformances: Vec<ConformanceStub>,
    pub child_types: IndexMap<Label, Symbol>,
    pub members: Members<T>,
}
