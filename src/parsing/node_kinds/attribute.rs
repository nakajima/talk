use derive_visitor::{Drive, DriveMut};

use crate::{impl_into_node, name::Name, node::Node, node_id::NodeID, parsing::span::Span};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Attribute {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(Attribute);
