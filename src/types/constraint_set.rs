use priority_queue::PriorityQueue;

use crate::{
    type_checker::TypeError,
    types::{
        constraint::{Constraint, ConstraintState},
        constraint_kind::ConstraintKind,
        row::Row,
        ty::Ty,
        type_var::TypeVar,
    },
};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub struct ConstraintId(pub usize);

impl ConstraintId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }
}

impl std::fmt::Display for ConstraintId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

#[derive(Default, Clone, Debug)]
pub struct ConstraintSet {
    free_type_vars: BTreeMap<TypeVar, Vec<ConstraintId>>,
    constraints: PriorityQueue<Constraint, usize>,
    last_id: usize,
}

impl ConstraintSet {
    pub fn new() -> Self {
        Self {
            free_type_vars: Default::default(),
            constraints: Default::default(),
            last_id: 0,
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

    pub fn next_id(&mut self) -> ConstraintId {
        self.last_id += 1;
        ConstraintId::new(self.last_id)
    }

    pub fn state_for(&self, id: &ConstraintId) -> Option<ConstraintState> {
        self.constraints.iter().find_map(|c| {
            if &c.0.id == id {
                return Some(c.0.state.clone());
            }

            None
        })
    }

    pub fn find(&self, id: &ConstraintId) -> Option<&Constraint> {
        self.constraints.iter().find_map(|c| {
            if &c.0.id == id {
                return Some(c.0);
            }

            None
        })
    }

    pub fn find_mut(&mut self, id: &ConstraintId) -> Option<&mut Constraint> {
        self.constraints.iter_mut().find_map(|c| {
            if &c.0.id == id {
                return Some(c.0);
            }

            None
        })
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

    pub fn row_constraints_for(&self, row: &Row) -> Result<Vec<&Constraint>, TypeError> {
        let constraints = self
            .constraints
            .iter()
            .filter_map(|(c, _)| {
                match &c.kind {
                    ConstraintKind::RowClosed { record } => {
                        if record == row {
                            return Some(c);
                        }
                    }
                    ConstraintKind::HasField { record, .. } => {
                        if record == row {
                            return Some(c);
                        }
                    }
                    ConstraintKind::TyHasField { receiver, .. } => {
                        if let Ty::Nominal { properties, .. } = receiver {
                            if *properties == *row {
                                return Some(c);
                            }
                        }
                    }
                    _ => (),
                }

                None
            })
            .collect();

        Ok(constraints)
    }
}
