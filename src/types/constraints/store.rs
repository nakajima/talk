use indexmap::IndexSet;
use petgraph::prelude::DiGraphMap;
use rustc_hash::FxHashMap;

use crate::{
    id_generator::IDGenerator,
    types::{
        constraints::constraint::Constraint,
        infer_ty::{InferTy, MetaVarId},
    },
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintId(u32);
impl From<u32> for ConstraintId {
    fn from(value: u32) -> Self {
        ConstraintId(value)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ConstraintStoreNode {
    Constraint(ConstraintId),
    Meta(MetaVarId),
}

#[derive(Clone, Copy)]
enum ConstraintStoreEdge {
    MetaDependency,
}

#[derive(Default)]
pub struct ConstraintStore {
    ids: IDGenerator,
    constraints: FxHashMap<ConstraintId, Constraint>,
    storage: DiGraphMap<ConstraintStoreNode, ConstraintStoreEdge>,

    wants: IndexSet<ConstraintId>,
    givens: IndexSet<ConstraintId>,
    deferred: IndexSet<ConstraintId>,
}

impl ConstraintStore {
    pub fn get(&self, id: &ConstraintId) -> &Constraint {
        self.constraints
            .get(id)
            .unwrap_or_else(|| unreachable!("did not find constraint"))
    }

    pub fn add(&mut self, constraint: Constraint) {
        let constraint_id: ConstraintId = self.ids.next_id();
        self.storage
            .add_node(ConstraintStoreNode::Constraint(constraint_id));

        for ty in constraint.collect_metas() {
            if let InferTy::Var { id, .. } = ty {
                let meta_id = ConstraintStoreNode::Meta(id);
                self.storage.add_node(meta_id);
                self.storage.add_edge(
                    meta_id,
                    ConstraintStoreNode::Constraint(constraint_id),
                    ConstraintStoreEdge::MetaDependency,
                );
            }
        }

        self.constraints.insert(constraint_id, constraint);
    }

    pub fn meta_dependents_for(&self, meta: MetaVarId) -> Vec<ConstraintId> {
        self.storage
            .neighbors(ConstraintStoreNode::Meta(meta))
            .filter_map(|n| {
                if let ConstraintStoreNode::Constraint(c) = n {
                    Some(c)
                } else {
                    None
                }
            })
            .collect()
    }
}

#[cfg(test)]
pub mod tests {
    use itertools::Itertools;

    use crate::{
        span::Span,
        types::{
            constraints::{constraint::ConstraintCause, equals::Equals},
            infer_ty::{InferTy, Level},
        },
    };

    use super::*;

    #[test]
    fn stores_constraint() {
        let mut store = ConstraintStore::default();
        let meta: MetaVarId = 1.into();
        let constraint = Constraint::Equals(Equals {
            lhs: InferTy::Var {
                id: meta,
                level: Level(1),
            },
            rhs: InferTy::Int,
            cause: ConstraintCause::Internal,
            span: Span::ANY,
        });

        store.add(constraint.clone());

        assert_eq!(
            store
                .meta_dependents_for(meta)
                .iter()
                .map(|id| store.get(id))
                .collect_vec(),
            vec![&constraint]
        )
    }
}
