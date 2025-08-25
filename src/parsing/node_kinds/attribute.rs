use crate::{name::Name, node_id::NodeID};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    pub id: NodeID,
    pub name: Name,
}
