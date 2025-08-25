use derive_visitor::{Drive, DriveMut};

use crate::{
    node_id::NodeID,
    node_kinds::{block::Block, pattern::Pattern},
};

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub struct MatchArm {
    #[drive(skip)]
    pub id: NodeID,
    pub pattern: Pattern,
    pub body: Block,
}
