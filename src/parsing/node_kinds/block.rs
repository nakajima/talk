use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, node::Node, node_id::NodeID, node_kinds::parameter::Parameter,
    parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Block {
    #[drive(skip)]
    pub id: NodeID,
    pub args: Vec<Parameter>,
    pub body: Vec<Node>,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(Block);
