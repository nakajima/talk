use crate::{impl_into_node, name::Name, node::Node, node_id::NodeID, parsing::span::Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    pub id: NodeID,
    pub name: Name,
    pub span: Span,
}

impl_into_node!(Attribute);
