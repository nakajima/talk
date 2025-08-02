use crate::types::constraint_set::ConstraintSet;

pub struct ConstraintSolver<'a> {
    pub constraints: &'a ConstraintSet,
}
