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
        conformance::ConformanceKey,
        constraint_solver::DeferralReason,
        constraints::{
            call::Call,
            conforms::Conforms,
            constraint::{Constraint, ConstraintCause},
            equals::Equals,
            has_field::HasField,
            member::Member,
            projection::Projection,
            type_member::TypeMember,
        },
        infer_row::InferRow,
        infer_ty::{InferTy, Level, Meta},
        solve_context::SolveContext,
    },
};

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum ConstraintPriority {
    Conforms,
    Call,
    Member,
    TypeMember,
    Projection,
    HasField,
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
    pub is_top_level: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintId(u32);
impl From<u32> for ConstraintId {
    fn from(value: u32) -> Self {
        ConstraintId(value)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ConstraintStoreNode {
    Constraint(ConstraintId),
    Meta(Meta),
    Symbol(Symbol),
    ConformanceKey(ConformanceKey),
}

impl std::fmt::Display for ConstraintStoreNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constraint(id) => write!(f, "constraint({id:?})"),
            Self::Meta(meta) => write!(f, "meta({meta:?})"),
            Self::Symbol(sym) => write!(f, "symbol({sym:?})"),
            Self::ConformanceKey(key) => write!(f, "conformancekey({key:?})"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[allow(clippy::enum_variant_names)]
pub(crate) enum ConstraintStoreEdge {
    MetaDependency,
    SymbolDependency,
    ConformanceDependency,
}

impl std::fmt::Display for ConstraintStoreEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Default, Debug)]
pub struct ConstraintStore {
    ids: IDGenerator,
    constraints: FxHashMap<ConstraintId, Constraint>,
    pub(crate) storage: DiGraphMap<ConstraintStoreNode, ConstraintStoreEdge>,
    pub(crate) meta: FxHashMap<ConstraintId, ConstraintMeta>,

    wants: PriorityQueue<ConstraintId, ConstraintPriority>,
    pub(crate) deferred: IndexSet<ConstraintId>,
    solved: IndexSet<ConstraintId>,
}

impl ConstraintStore {
    pub fn worklist(&mut self) -> IndexSet<ConstraintId> {
        std::mem::take(&mut self.wants)
            .into_sorted_iter()
            .map(|w| w.0)
            .collect()
    }

    pub fn unsolved(&self) -> Vec<&Constraint> {
        self.deferred.iter().map(|d| self.get(d)).collect()
    }

    pub fn get(&self, id: &ConstraintId) -> &Constraint {
        self.constraints
            .get(id)
            .unwrap_or_else(|| unreachable!("did not find constraint"))
    }

    pub fn copy_group(&self, id: ConstraintId) -> BindingGroup {
        let existing = self.meta.get(&id).unwrap_or_else(|| unreachable!());
        BindingGroup {
            id: existing.group_id,
            level: existing.level,
            binders: Default::default(),
            is_top_level: existing.is_top_level,
        }
    }

    pub fn is_stalled(&self) -> bool {
        self.wants.is_empty()
    }

    #[instrument(skip(self))]
    pub fn defer(&mut self, id: ConstraintId, reason: DeferralReason) {
        self.deferred.insert(id);
        let constraint_node = ConstraintStoreNode::Constraint(id);
        match reason {
            DeferralReason::WaitingOnConformance(key) => {
                let meta_node = ConstraintStoreNode::ConformanceKey(key);
                self.storage.add_node(meta_node);
                self.storage.add_edge(
                    meta_node,
                    constraint_node,
                    ConstraintStoreEdge::ConformanceDependency,
                );
            }
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
            DeferralReason::WaitingOnSymbols(symbols) => {
                for symbol in symbols {
                    let sym_node = ConstraintStoreNode::Symbol(symbol);
                    self.storage.add_node(sym_node);
                    self.storage.add_edge(
                        sym_node,
                        constraint_node,
                        ConstraintStoreEdge::SymbolDependency,
                    );
                }
            }
            DeferralReason::Multi(reasons) => {
                for reason in reasons {
                    self.defer(id, reason);
                }
            }
            DeferralReason::Unknown => {}
        }
    }

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
            let group = self.meta.get(id).unwrap_or_else(|| unreachable!()).group_id;
            if group != context.group {
                continue;
            }

            if self.solved.contains(id) {
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

    #[instrument(skip(self))]
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
    pub fn wake_conformances(&mut self, keys: &[ConformanceKey]) {
        let mut awakened = IndexSet::<ConstraintId>::default();
        for key in keys {
            awakened.extend(self.conformance_dependents_for(*key));
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
                is_top_level: group.is_top_level,
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

    pub fn conformance_dependents_for(&self, key: ConformanceKey) -> Vec<ConstraintId> {
        self.storage
            .neighbors(ConstraintStoreNode::ConformanceKey(key))
            .filter_map(|n| {
                if let ConstraintStoreNode::Constraint(c) = n {
                    Some(c)
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn constraint_symbol_dependents_for(&self, constraint_id: ConstraintId) -> Vec<Symbol> {
        self.storage
            .neighbors(ConstraintStoreNode::Constraint(constraint_id))
            .filter_map(|n| {
                if let ConstraintStoreNode::Symbol(symbol) = n {
                    Some(symbol)
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
            Constraint::Equals(Equals {
                id,
                node_id: None,
                lhs,
                rhs,
                cause: None,
            }),
            &BindingGroup {
                id: Default::default(),
                level: Default::default(),
                binders: Default::default(),
                is_top_level: Default::default(),
            },
        )
    }

    pub fn wants_equals_at(
        &mut self,
        node_id: NodeID,
        lhs: InferTy,
        rhs: InferTy,
        group: &BindingGroup,
    ) -> &Constraint {
        self.wants_equals_at_with_cause(node_id, lhs, rhs, group, None)
    }

    pub fn wants_equals_at_with_cause(
        &mut self,
        node_id: NodeID,
        lhs: InferTy,
        rhs: InferTy,
        group: &BindingGroup,
        cause: Option<ConstraintCause>,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::Equals(Equals {
                id,
                node_id: Some(node_id),
                lhs,
                rhs,
                cause,
            }),
            group,
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

    pub fn wants_conforms(
        &mut self,
        conformance_node_id: NodeID,
        ty: InferTy,
        protocol_id: ProtocolId,
        group: &BindingGroup,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::Conforms(Conforms {
                id,
                conformance_node_id,
                ty,
                protocol_id,
            }),
            group,
        )
    }

    pub fn _has_field(
        &mut self,
        row: InferRow,
        label: Label,
        ty: InferTy,
        node_id: Option<NodeID>,
        group: &BindingGroup,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::HasField(HasField {
                id,
                node_id,
                row,
                label,
                ty,
            }),
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

    #[allow(clippy::too_many_arguments)]
    pub fn wants_type_member(
        &mut self,
        base: InferTy,
        name: Label,
        generics: Vec<InferTy>,
        result: InferTy,
        node_id: NodeID,
        group: &BindingGroup,
        cause: ConstraintCause,
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
                cause,
            }),
            group,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn wants_call(
        &mut self,
        call_node_id: NodeID,
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
                call_node_id,
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
            infer_ty::{InferTy, Level, MetaVarId},
        },
    };

    use super::*;

    #[test]
    fn stores_constraint() {
        let mut store = ConstraintStore::default();
        let meta: MetaVarId = 1.into();
        let constraint = Constraint::Equals(Equals {
            id: 1.into(),
            node_id: None,
            lhs: InferTy::Var {
                id: meta,
                level: Level(1),
            },
            rhs: InferTy::Int,
            cause: None,
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
            node_id: None,
            lhs: InferTy::Var {
                id: meta,
                level: Level(1),
            },
            rhs: InferTy::Int,
            cause: None,
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
            node_id: None,
            lhs: InferTy::Var {
                id: meta,
                level: Level(1),
            },
            rhs: InferTy::Int,
            cause: None,
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
