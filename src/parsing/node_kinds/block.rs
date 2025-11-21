use derive_visitor::{Drive, DriveMut};

use crate::{impl_into_node, name::Name, node::Node, node_id::NodeID, parsing::span::Span};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Block {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub args: Vec<Name>,
    pub body: Vec<Node>,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(Block);
