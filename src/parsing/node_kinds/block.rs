use crate::{parsing::span::Span, impl_into_node, name::Name, node::Node, node_id::NodeID};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub id: NodeID,
    pub args: Vec<Name>,
    pub body: Vec<Node>,
    pub span: Span,
}

impl_into_node!(Block);
