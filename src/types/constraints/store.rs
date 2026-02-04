use indexmap::IndexSet;
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
            default_ty::DefaultTy,
            equals::Equals,
            has_field::HasField,
            member::Member,
            projection::Projection,
            row_subset::RowSubset,
            type_member::TypeMember,
        },
        infer_row::Row,
        infer_ty::{Level, Meta, Ty},
        solve_context::SolveContext,
        variational::Configuration,
    },
};

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum ConstraintPriority {
    DefaultTy,
    RowSubset,
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
            Constraint::RowSubset(..) => ConstraintPriority::RowSubset,
            Constraint::DefaultTy(..) => ConstraintPriority::DefaultTy,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintMeta {
    pub id: ConstraintId,
    pub group_id: GroupId,
    pub level: Level,
    pub is_top_level: bool,
    /// The configuration (world) in which this constraint applies.
    /// Universal configuration means the constraint applies in all worlds.
    pub config: Configuration,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub struct ConstraintId(u32);
impl From<u32> for ConstraintId {
    fn from(value: u32) -> Self {
        ConstraintId(value)
    }
}

#[derive(Default, Debug)]
pub struct ConstraintStore {
    ids: IDGenerator,
    constraints: FxHashMap<ConstraintId, Constraint>,
    pub(crate) meta: FxHashMap<ConstraintId, ConstraintMeta>,

    // Dependency tracking: maps from dependency key to constraints waiting on it
    meta_deps: FxHashMap<Meta, Vec<ConstraintId>>,
    symbol_deps: FxHashMap<Symbol, Vec<ConstraintId>>,
    conformance_deps: FxHashMap<ConformanceKey, Vec<ConstraintId>>,

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
            config: existing.config.clone(),
        }
    }

    pub fn is_stalled(&self) -> bool {
        self.wants.is_empty()
    }

    #[instrument(skip(self))]
    pub fn defer(&mut self, id: ConstraintId, reason: DeferralReason) {
        self.deferred.insert(id);
        match reason {
            DeferralReason::WaitingOnConformance(key) => {
                self.conformance_deps.entry(key).or_default().push(id);
            }
            DeferralReason::WaitingOnMeta(meta) => {
                self.meta_deps.entry(meta).or_default().push(id);
            }
            DeferralReason::WaitingOnSymbol(symbol) => {
                self.symbol_deps.entry(symbol).or_default().push(id);
            }
            DeferralReason::WaitingOnSymbols(symbols) => {
                for symbol in symbols {
                    self.symbol_deps.entry(symbol).or_default().push(id);
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
        // Note: We don't remove the constraint from dependency maps here.
        // The lookup methods will filter out solved constraints.
    }

    #[instrument(skip(self))]
    pub fn generalizable_for(&self, context: &SolveContext) -> IndexSet<Constraint> {
        let mut res = IndexSet::default();
        for (id, constraint) in self.constraints.iter() {
            let group = self.meta.get(id).unwrap_or_else(|| unreachable!()).group_id;
            if group != context.group() {
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
        self.wants.push(constraint_id, constraint.priority());
        self.meta.insert(
            constraint_id,
            ConstraintMeta {
                id: constraint_id,
                group_id: group.id,
                level: group.level,
                is_top_level: group.is_top_level,
                config: group.config.clone(),
            },
        );

        // Track meta variable dependencies for wake-up on solve
        for ty in constraint.collect_metas() {
            if let Ty::Var { id, .. } = ty {
                self.meta_deps
                    .entry(Meta::Ty(id))
                    .or_default()
                    .push(constraint_id);
            }
        }

        self.constraints.insert(constraint_id, constraint);
        self.constraints
            .get(&constraint_id)
            .unwrap_or_else(|| unreachable!())
    }

    pub fn meta_dependents_for(&self, meta: Meta) -> Vec<ConstraintId> {
        self.meta_deps.get(&meta).cloned().unwrap_or_default()
    }

    pub fn symbol_dependents_for(&self, symbol: Symbol) -> Vec<ConstraintId> {
        self.symbol_deps.get(&symbol).cloned().unwrap_or_default()
    }

    pub fn conformance_dependents_for(&self, key: ConformanceKey) -> Vec<ConstraintId> {
        self.conformance_deps.get(&key).cloned().unwrap_or_default()
    }
}

// Helpers
impl ConstraintStore {
    pub fn wants_default(
        &mut self,
        node_id: NodeID,
        var: Ty,
        ty: Ty,
        allowed: Vec<Ty>,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::DefaultTy(DefaultTy {
                id,
                node_id,
                var,
                ty,
                allowed,
                cause: ConstraintCause::Literal(node_id),
            }),
            &Default::default(),
        )
    }

    pub fn wants_equals(&mut self, lhs: Ty, rhs: Ty) -> &Constraint {
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
                config: Configuration::universal(),
            },
        )
    }

    pub fn wants_equals_at(
        &mut self,
        node_id: NodeID,
        lhs: Ty,
        rhs: Ty,
        group: &BindingGroup,
    ) -> &Constraint {
        self.wants_equals_at_with_cause(node_id, lhs, rhs, group, None)
    }

    pub fn wants_equals_at_with_cause(
        &mut self,
        node_id: NodeID,
        lhs: Ty,
        rhs: Ty,
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
        base: Ty,
        label: Label,
        protocol_id: Option<ProtocolId>,
        result: Ty,
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
        ty: Ty,
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
        row: Row,
        label: Label,
        ty: Ty,
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
        receiver: Ty,
        label: Label,
        ty: Ty,
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
        base: Ty,
        name: Label,
        generics: Vec<Ty>,
        result: Ty,
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
        callee: Ty,
        args: Vec<Ty>,
        type_args: Vec<Ty>,
        returns: Ty,
        callee_type: Ty,
        receiver: Option<Ty>,
        group: &BindingGroup,
        effect_context_row: Row,
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
                callee_type,
                receiver,
                effect_context_row,
            }),
            group,
        )
    }

    pub fn wants_row_subset(
        &mut self,
        node_id: Option<NodeID>,
        left: Row,
        right: Row,
        group: &BindingGroup,
    ) -> &Constraint {
        let id = self.ids.next_id();
        self.wants(
            id,
            Constraint::RowSubset(RowSubset {
                id,
                node_id,
                left,
                right,
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
            infer_ty::{Level, MetaVarId, Ty},
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
            lhs: Ty::Var {
                id: meta,
                level: Level(1),
            },
            rhs: Ty::Int,
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
            lhs: Ty::Var {
                id: meta,
                level: Level(1),
            },
            rhs: Ty::Int,
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
            lhs: Ty::Var {
                id: meta,
                level: Level(1),
            },
            rhs: Ty::Int,
            cause: None,
        });

        let member = Constraint::Member(Member {
            id: 2.into(),
            node_id: NodeID::ANY,
            receiver: Ty::Int,
            label: "fizz".into(),
            ty: Ty::Var {
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
