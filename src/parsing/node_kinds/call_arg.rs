use crate::{
    parsing::span::Span, impl_into_node, label::Label, node::Node, node_id::NodeID, node_kinds::expr::Expr,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallArg {
    pub id: NodeID,
    pub label: Label,
    pub value: Expr,
    pub span: Span,
}

impl_into_node!(CallArg);
