use crate::{
    parsing::span::Span,
    impl_into_node,
    node::Node,
    node_id::NodeID,
    node_kinds::{block::Block, pattern::Pattern},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pub id: NodeID,
    pub pattern: Pattern,
    pub body: Block,
    pub span: Span,
}

impl_into_node!(MatchArm);
