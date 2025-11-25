use indexmap::IndexSet;
use itertools::Itertools;
use petgraph::prelude::DiGraphMap;
use priority_queue::PriorityQueue;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    id_generator::IDGenerator,
    label::Label,
    name_resolution::{
        scc_graph::BindingGroup,
        symbol::{ProtocolId, Symbol},
    },
    node_id::NodeID,
    types::{
        constraint_solver::DeferralReason,
        constraints::{
            call::Call, conforms::Conforms, constraint::Constraint, equals::Equals,
            has_field::HasField, member::Member, projection::Projection, type_member::TypeMember,
        },
        infer_row::InferRow,
        infer_ty::{InferTy, Level, Meta, MetaVarId},
        passes::inference_pass::GeneralizationBlock,
        solve_context::SolveContext,
        type_operations::UnificationSubstitutions,
    },
};

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum ConstraintPriority {
    Conforms,
    Member,
    TypeMember,
    Projection,
    HasField,
    Call,
    Equals,
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GroupId(pub u32);

impl Constraint {
    fn priority(&self) -> ConstraintPriority {
        match self {
            Constraint::Call(..) => ConstraintPriority::Call,
            Constraint::Equals(..) => ConstraintPriority::Equals,
            Constraint::HasField(..) => ConstraintPriority::HasField,
            Constraint::Member(..) => ConstraintPriority::Member,
            Constraint::Conforms(..) => ConstraintPriority::Conforms,
            Constraint::TypeMember(..) => ConstraintPriority::TypeMember,
            Constraint::Projection(..) => ConstraintPriority::Projection,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstraintMeta {
    pub id: ConstraintId,
    pub group_id: GroupId,
    pub level: Level,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintId(u32);
impl From<u32> for ConstraintId {
    fn from(value: u32) -> Self {
        ConstraintId(value)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ConstraintStoreNode {
    Constraint(ConstraintId),
    Meta(Meta),
    Symbol(Symbol),
}

#[derive(Debug, Clone, Copy)]
enum ConstraintStoreEdge {
    MetaDependency,
    SymbolDependency,
}

#[derive(Default, Debug)]
pub struct ConstraintStore {
    ids: IDGenerator,
    constraints: FxHashMap<ConstraintId, Constraint>,
    storage: DiGraphMap<ConstraintStoreNode, ConstraintStoreEdge>,
    pub(crate) meta: FxHashMap<ConstraintId, ConstraintMeta>,

    wants: PriorityQueue<ConstraintId, ConstraintPriority>,
    givens: IndexSet<ConstraintId>,
    pub(crate) deferred: IndexSet<ConstraintId>,
    solved: IndexSet<ConstraintId>,

    generalization_blocks: FxHashMap<MetaVarId, GeneralizationBlock>,
}

impl ConstraintStore {
    pub fn worklist(&mut self) -> IndexSet<ConstraintId> {
        std::mem::take(&mut self.wants)
            .into_sorted_iter()
            .map(|w| w.0)
            .collect()
    }

    pub fn get(&self, id: &ConstraintId) -> &Constraint {
        self.constraints
            .get(id)
            .unwrap_or_else(|| unreachable!("did not find constraint"))
    }

    pub fn copy_group(&self, id: ConstraintId) -> BindingGroup {
        BindingGroup {
            id: self
                .meta
                .get(&id)
                .unwrap_or_else(|| unreachable!())
                .group_id,
            level: self.meta.get(&id).unwrap_or_else(|| unreachable!()).level,
            binders: Default::default(),
        }
    }

    pub fn is_stalled(&self) -> bool {
        self.wants.is_empty()
    }

    #[instrument(skip(self))]
    pub fn defer(&mut self, id: ConstraintId, reason: DeferralReason) {
        tracing::debug!("defer constraint {:?}: {:?}", id, self.get(&id));
        self.deferred.insert(id);
        let constraint_node = ConstraintStoreNode::Constraint(id);
        match reason {
            DeferralReason::WaitingOnMeta(meta) => {
                let meta_node = ConstraintStoreNode::Meta(meta);
                self.storage.add_node(meta_node);
                self.storage.add_edge(
                    meta_node,
                    constraint_node,
                    ConstraintStoreEdge::MetaDependency,
                );
            }
            DeferralReason::WaitingOnSymbol(symbol) => {
                let sym_node = ConstraintStoreNode::Symbol(symbol);
                self.storage.add_node(sym_node);
                self.storage.add_edge(
                    sym_node,
                    constraint_node,
                    ConstraintStoreEdge::SymbolDependency,
                );
            }
            DeferralReason::Unknown => {}
        }
    }

    #[instrument(skip(self))]
    pub fn solve(&mut self, id: ConstraintId) {
        tracing::debug!("solve constraint {:?}: {:?}", id, self.get(&id));
        self.deferred.swap_remove(&id);
        self.solved.insert(id);
        let constraint_node = ConstraintStoreNode::Constraint(id);
        let edges = self
            .storage
            .edges_directed(constraint_node, petgraph::Direction::Incoming)
            .map(|(_, other, _)| other)
            .collect_vec();
        for other in edges {
            self.storage.remove_edge(constraint_node, other);
            self.storage.remove_edge(other, constraint_node);
        }
    }

    #[instrument(skip(self))]
    pub fn generalizable_for(&self, context: &SolveContext) -> IndexSet<Constraint> {
        let mut res = IndexSet::default();
        for (id, constraint) in self.constraints.iter() {
            println!("considering {:?}", constraint);
            let group = self.meta.get(id).unwrap_or_else(|| unreachable!()).group_id;
            if group != context.group {
                println!(
                    "wrong group: {group:?} (context group is {:?}, skipping",
                    context.group
                );
                continue;
            }

            if self.solved.contains(id) {
                println!("constraint is solved, skipping");
                continue;
            }

            res.insert(constraint.clone());
        }
        res
    }

    #[instrument(skip(self))]
    pub fn wake_metas(&mut self, metas: &[Meta]) {
        let mut awakened = IndexSet::<ConstraintId>::default();
        for meta in metas {
            awakened.extend(self.meta_dependents_for(*meta));
        }
        tracing::trace!("waking constraints: {awakened:?}");
        for constraint_id in awakened {
            if self.solved.contains(&constraint_id) {
                continue;
            }

            self.deferred.swap_remove(&constraint_id);
            self.wants.push(constraint_id, ConstraintPriority::Equals);
        }
    }

    #[instrument(skip(self), ret)]
    pub fn wake_symbols(&mut self, symbols: &[Symbol]) {
        let mut awakened = IndexSet::<ConstraintId>::default();
        for symbol in symbols {
            if matches!(symbol, Symbol::Global(..)) {
                continue;
            }
            awakened.extend(self.symbol_dependents_for(*symbol));
        }

        for constraint_id in awakened {
            if self.solved.contains(&constraint_id) {
                continue;
            }
            self.deferred.swap_remove(&constraint_id);
            self.wants.push(constraint_id, ConstraintPriority::Equals);
        }
    }

    #[instrument(skip(self))]
    pub fn wants(
        &mut self,
        constraint_id: ConstraintId,
        constraint: Constraint,
        group: &BindingGroup,
    ) -> &Constraint {
        self.storage
            .add_node(ConstraintStoreNode::Constraint(constraint_id));

        self.wants.push(constraint_id, constraint.priority());
        self.meta.insert(
            constraint_id,
            ConstraintMeta {
                id: constraint_id,
                group_id: group.id,
                level: group.level,
            },
        );

        for ty in constraint.collect_metas() {
            if let InferTy::Var { id, .. } = ty {
                let meta_id = ConstraintStoreNode::Meta(Meta::Ty(id));
                self.storage.add_node(meta_id);
                self.storage.add_edge(
                    meta_id,
                    ConstraintStoreNode::Constraint(constraint_id),
                    ConstraintStoreEdge::MetaDependency,
                );
            }
        }

        self.constraints.insert(constraint_id, constraint);
        self.constraints
            .get(&constraint_id)
            .unwrap_or_else(|| unreachable!())
    }

    pub fn meta_dependents_for(&self, meta: Meta) -> Vec<ConstraintId> {
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

    pub fn symbol_dependents_for(&self, symbol: Symbol) -> Vec<ConstraintId> {
        self.storage
            .neighbors(ConstraintStoreNode::Symbol(symbol))
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

// Helpers
impl ConstraintStore {
    pub fn wants_equals(&mut self, lhs: InferTy, rhs: InferTy) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::Equals(Equals { id, lhs, rhs }),
            &BindingGroup {
                id: Default::default(),
                level: Default::default(),
                binders: Default::default(),
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn wants_projection(
        &mut self,
        node_id: NodeID,
        base: InferTy,
        label: Label,
        protocol_id: Option<ProtocolId>,
        result: InferTy,
        group: &BindingGroup,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::Projection(Projection {
                id,
                node_id,
                base,
                protocol_id,
                label,
                result,
            }),
            group,
        )
    }

    pub fn wants_conforms(&mut self, ty: InferTy, protocol_id: ProtocolId) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::Conforms(Conforms {
                id,
                ty,
                protocol_id,
            }),
            &Default::default(),
        )
    }

    pub fn _has_field(
        &mut self,
        row: InferRow,
        label: Label,
        ty: InferTy,
        group: &BindingGroup,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::HasField(HasField { id, row, label, ty }),
            group,
        )
    }

    pub fn wants_member(
        &mut self,
        node_id: NodeID,
        receiver: InferTy,
        label: Label,
        ty: InferTy,
        group: &BindingGroup,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::Member(Member {
                id,
                node_id,
                receiver,
                label,
                ty,
            }),
            group,
        )
    }

    pub fn wants_type_member(
        &mut self,
        base: InferTy,
        name: Label,
        generics: Vec<InferTy>,
        result: InferTy,
        node_id: NodeID,
        group: &BindingGroup,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::TypeMember(TypeMember {
                id,
                node_id,
                base,
                name,
                generics,
                result,
            }),
            group,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn wants_call(
        &mut self,
        callee_id: NodeID,
        callee: InferTy,
        args: Vec<InferTy>,
        type_args: Vec<InferTy>,
        returns: InferTy,
        receiver: Option<InferTy>,
        group: &BindingGroup,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::Call(Call {
                id,
                callee_id,
                callee,
                args,
                type_args,
                returns,
                receiver,
            }),
            group,
        )
    }
}

#[cfg(test)]
pub mod tests {
    use itertools::Itertools;

    use crate::{
        node_id::NodeID,
        types::{
            constraints::{equals::Equals, member::Member},
            infer_ty::{InferTy, Level},
        },
    };

    use super::*;

    #[test]
    fn stores_constraint() {
        let mut store = ConstraintStore::default();
        let meta: MetaVarId = 1.into();
        let constraint = Constraint::Equals(Equals {
            id: 1.into(),
            lhs: InferTy::Var {
                id: meta,
                level: Level(1),
            },
            rhs: InferTy::Int,
        });

        store.wants(1.into(), constraint.clone(), &Default::default());

        assert_eq!(
            store
                .meta_dependents_for(Meta::Ty(meta))
                .iter()
                .map(|id| store.get(id))
                .collect_vec(),
            vec![&constraint]
        )
    }

    #[test]
    fn gets_constraints_to_solve() {
        let mut store = ConstraintStore::default();
        let meta: MetaVarId = 1.into();
        let constraint = Constraint::Equals(Equals {
            id: 1.into(),
            lhs: InferTy::Var {
                id: meta,
                level: Level(1),
            },
            rhs: InferTy::Int,
        });

        store.wants(1.into(), constraint.clone(), &Default::default());

        assert_eq!(Some(ConstraintId(1)), store.worklist().first().copied());
    }

    #[test]
    fn gets_equals_first() {
        let mut store = ConstraintStore::default();
        let meta: MetaVarId = 1.into();
        let equals = Constraint::Equals(Equals {
            id: 1.into(),
            lhs: InferTy::Var {
                id: meta,
                level: Level(1),
            },
            rhs: InferTy::Int,
        });

        let member = Constraint::Member(Member {
            id: 2.into(),
            node_id: NodeID::ANY,
            receiver: InferTy::Int,
            label: "fizz".into(),
            ty: InferTy::Var {
                id: 1.into(),
                level: Level(1),
            },
        });

        store.wants(1.into(), member, &Default::default());
        store.wants(2.into(), equals, &Default::default());

        assert_eq!(
            Some(ConstraintId(2)),
            store.worklist().iter().next().copied()
        );
    }
}
