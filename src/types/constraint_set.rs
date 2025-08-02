use crate::types::{constraint::Constraint, type_var::TypeVar};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug)]
pub struct ConstraintId(usize);

#[derive(Default, Clone, Debug)]
pub struct ConstraintSet {
    free_type_vars: BTreeMap<TypeVar, Vec<ConstraintId>>,
    constraints: Vec<Constraint>,
}

impl ConstraintSet {
    pub fn new() -> Self {
        Self {
            free_type_vars: Default::default(),
            constraints: Default::default(),
        }
    }

    pub fn add(&mut self, constraint: Constraint) -> ConstraintId {
        let id = ConstraintId(self.constraints.len());

        for type_var in &constraint.type_vars() {
            self.free_type_vars
                .entry(*type_var)
                .and_modify(|curr| curr.push(id))
                .or_insert(vec![id]);
        }

        self.constraints.push(constraint);

        id
    }
}
