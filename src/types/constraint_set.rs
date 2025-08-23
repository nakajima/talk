use priority_queue::PriorityQueue;

use crate::{
    expr_id::ExprID,
    type_checker::TypeError,
    types::{
        constraint::{Constraint, ConstraintCause, ConstraintState},
        constraint_kind::ConstraintKind,
        row::Row,
        ty::{Ty, TypeParameter},
        type_var::{TypeVar, TypeVarKind},
        type_var_context::RowVar,
        visitors::inference_visitor::Substitutions,
    },
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstraintId(pub usize);

impl ConstraintId {
    pub const GENERIC: ConstraintId = ConstraintId(usize::MAX);

    pub fn new(id: usize) -> Self {
        Self(id)
    }
}

impl std::fmt::Debug for ConstraintId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if *self == Self::GENERIC {
            write!(f, "ConstraintId::GENERIC")
        } else {
            write!(f, "ConstraintId({})", self.0)
        }
    }
}

impl std::fmt::Display for ConstraintId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum GenericConstraintKey {
    TypeParameter(TypeParameter),
    RowVar(RowVar),
}

#[derive(Default, Clone, Debug)]
pub struct ConstraintSet {
    free_type_vars: BTreeMap<TypeVar, Vec<ConstraintId>>,
    constraints: PriorityQueue<Constraint, usize>,
    relationships: BTreeMap<ConstraintId, Vec<ConstraintId>>,
    // Any time a constraint is added with canonical vars, we store it in here. When we instantiate,
    // we look to see if any of the constraints in here contain any of the canonical vars of the type
    // we are instantiating. If so, we'll instantiate a copy of those constraints as well.
    generic_constraints: BTreeMap<ConstraintId, Constraint>,
    generic_constraints_index: BTreeMap<GenericConstraintKey, BTreeSet<ConstraintId>>,
    last_id: usize,
}

impl ConstraintSet {
    pub fn new() -> Self {
        Self {
            free_type_vars: Default::default(),
            constraints: Default::default(),
            relationships: Default::default(),
            generic_constraints: Default::default(),
            generic_constraints_index: Default::default(),
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

    pub(crate) fn instantiate_type_parameter(
        &self,
        type_parameter: TypeParameter,
        substitutions: &Substitutions,
    ) -> Result<Vec<Constraint>, TypeError> {
        let Some(matching_constraint_ids) = self
            .generic_constraints_index
            .get(&GenericConstraintKey::TypeParameter(type_parameter))
        else {
            return Ok(vec![]);
        };

        matching_constraint_ids
            .iter()
            .map(|id| {
                self.generic_constraints
                    .get(id)
                    .unwrap()
                    .clone()
                    .instantiate(substitutions)
            })
            .collect::<Result<Vec<_>, _>>()
    }

    pub(crate) fn instantiate_row_var(
        &self,
        row_var: RowVar,
        substitutions: &Substitutions,
    ) -> Result<Vec<Constraint>, TypeError> {
        let Some(matching_constraint_ids) = self
            .generic_constraints_index
            .get(&GenericConstraintKey::RowVar(row_var))
        else {
            return Ok(vec![]);
        };

        matching_constraint_ids
            .iter()
            .map(|id| {
                self.generic_constraints
                    .get(id)
                    .unwrap()
                    .clone()
                    .instantiate(substitutions)
            })
            .collect::<Result<Vec<_>, _>>()
    }

    pub fn children(&self, parent: &Constraint) -> impl Iterator<Item = &Constraint> {
        let child_ids = self
            .relationships
            .get(&parent.id)
            .cloned()
            .unwrap_or_default();

        self.constraints.iter().filter_map(move |(c, _)| {
            if child_ids.contains(&c.id) {
                Some(c)
            } else {
                None
            }
        })
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

    pub fn to_vec(mut self) -> Vec<Constraint> {
        self.constraints.drain().map(|c| c.0).collect()
    }

    pub fn into_iter(self) -> impl Iterator<Item = Constraint> {
        self.constraints.into_iter().map(|c| c.0)
    }

    pub fn constrain(
        &mut self,
        expr_id: ExprID,
        kind: ConstraintKind,
        cause: ConstraintCause,
    ) -> ConstraintId {
        let id = self.next_id();

        tracing::trace!("Constraining {id:?} kind: {kind} cause: {cause:?}");

        self.add(Constraint {
            id,
            expr_id,
            cause,
            kind,
            state: ConstraintState::Pending,
        });

        id
    }

    pub fn add_child(&mut self, parent: ConstraintId, child: ConstraintId) {}

    pub fn extend(&mut self, constraints: &ConstraintSet) {
        for (constraint, _) in constraints.constraints.iter() {
            self.add(constraint.clone());
        }
    }

    pub fn add(&mut self, mut constraint: Constraint) -> ConstraintId {
        // If the constraint has a generic ID, assign it a real ID
        if constraint.id == ConstraintId::GENERIC {
            constraint.id = self.next_id();
        }

        let constraint_id = constraint.id;

        let index_keys = constraint.generic_index_keys();
        if !index_keys.is_empty() {
            tracing::trace!("stashing generic constraint {constraint}");

            self.generic_constraints
                .entry(constraint_id)
                .or_insert(constraint);

            for key in index_keys.iter() {
                self.generic_constraints_index
                    .entry(*key)
                    .or_default()
                    .insert(constraint_id);
            }

            return constraint_id;
        }

        let priority = constraint.priority();

        tracing::trace!("adding non-generic constraint: {constraint}");

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
                        if let Ty::Nominal { properties, .. } = receiver
                            && *properties == *row
                        {
                            return Some(c);
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
