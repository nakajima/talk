use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    node_id::NodeID,
    node_kinds::{block::Block, pattern::Pattern},
    parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct MatchArm {
    #[drive(skip)]
    pub id: NodeID,
    pub pattern: Pattern,
    pub body: Block,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(MatchArm);
