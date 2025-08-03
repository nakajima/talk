use priority_queue::PriorityQueue;

use crate::types::{constraint::Constraint, type_var::TypeVar};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub struct ConstraintId(usize);

impl ConstraintId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }
}

#[derive(Default, Clone, Debug)]
pub struct ConstraintSet {
    free_type_vars: BTreeMap<TypeVar, Vec<ConstraintId>>,
    constraints: PriorityQueue<Constraint, usize>,
}

impl ConstraintSet {
    pub fn new() -> Self {
        Self {
            free_type_vars: Default::default(),
            constraints: Default::default(),
        }
    }

    pub fn pop(&mut self) -> Option<Constraint> {
        self.constraints.pop().map(|c| c.0)
    }

    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Constraint> {
        self.constraints.iter_mut().map(|f| f.0)
    }

    pub fn next_id(&self) -> ConstraintId {
        ConstraintId::new(self.constraints.len())
    }

    pub fn add(&mut self, constraint: Constraint) -> ConstraintId {
        let constraint_id = constraint.id;
        let priority = constraint.priority();

        for type_var in &constraint.type_vars() {
            self.free_type_vars
                .entry(*type_var)
                .and_modify(|curr| curr.push(constraint_id))
                .or_insert(vec![constraint_id]);
        }

        self.constraints.push(constraint, priority);

        constraint_id
    }
}
