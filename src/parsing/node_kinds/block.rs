use derive_visitor::{Drive, DriveMut};

use crate::{name::Name, node::Node, node_id::NodeID};

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub struct Block {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub args: Vec<Name>,
    pub body: Vec<Node>,
}
