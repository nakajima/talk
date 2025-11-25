use crate::types::{constraints::store::ConstraintId, infer_ty::InferTy};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Equals {
    pub id: ConstraintId,
    pub lhs: InferTy,
    pub rhs: InferTy,
}
