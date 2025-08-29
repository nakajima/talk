use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, name::Name, node::Node, node_id::NodeID, node_kinds::expr::Expr,
    parsing::span::Span,
};

// Single field in a record literal
#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct RecordField {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Name,
    pub value: Expr,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(RecordField);
