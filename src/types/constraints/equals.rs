use crate::node_id::NodeID;
use crate::types::{
    constraints::{constraint::ConstraintCause, store::ConstraintId},
    infer_ty::Ty,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Equals {
    pub id: ConstraintId,
    pub node_id: Option<NodeID>,
    pub lhs: Ty,
    pub rhs: Ty,
    pub cause: Option<ConstraintCause>,
}
