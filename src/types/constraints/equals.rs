use crate::node_id::NodeID;
use crate::types::{
    constraints::{constraint::ConstraintCause, store::ConstraintId},
    infer_ty::InferTy,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Equals {
    pub id: ConstraintId,
    pub node_id: Option<NodeID>,
    pub lhs: InferTy,
    pub rhs: InferTy,
    pub cause: Option<ConstraintCause>,
}
