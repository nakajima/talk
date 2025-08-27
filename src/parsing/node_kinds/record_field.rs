use crate::{
    parsing::span::Span, impl_into_node, name::Name, node::Node, node_id::NodeID, node_kinds::expr::Expr,
};

// Single field in a record literal
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordField {
    pub id: NodeID,
    pub label: Name,
    pub value: Expr,
    pub span: Span,
}

impl_into_node!(RecordField);
