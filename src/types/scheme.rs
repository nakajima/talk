use derive_visitor::{Drive, DriveMut};
use indexmap::IndexSet;
use itertools::Itertools;
use tracing::instrument;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    types::{
        constraints::store::ConstraintStore,
        infer_row::{Row, RowParamId},
        infer_ty::{Level, Ty},
        predicate::Predicate,
        solve_context::SolveContext,
        type_operations::{InstantiationSubstitutions, instantiate_ty},
        type_session::TypeSession,
    },
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ForAll {
    Ty(Symbol),
    Row(RowParamId),
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct Scheme {
    #[drive(skip)]
    pub(crate) foralls: IndexSet<ForAll>,
    #[drive(skip)]
    pub(crate) predicates: Vec<Predicate>,
    pub(crate) ty: Ty,
}

impl std::hash::Hash for Scheme {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ty.hash(state);
        for forall in self.foralls.iter() {
            forall.hash(state);
        }
    }
}

impl Scheme {
    fn bounds_for(&self, param: &Symbol) -> Vec<ProtocolId> {
        let mut bounds: IndexSet<ProtocolId> = IndexSet::default();

        for predicate in &self.predicates {
            if let Predicate::Conforms {
                param: predicate_param,
                protocol_id,
            } = predicate
                && predicate_param == param
            {
                bounds.insert(*protocol_id);
            }
        }

        for predicate in self.ty.collect_param_predicates() {
            if let Predicate::Conforms {
                param: predicate_param,
                protocol_id,
            } = predicate
                && &predicate_param == param
            {
                bounds.insert(protocol_id);
            }
        }

        bounds.into_iter().collect()
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        Self {
            foralls: self.foralls,
            predicates: self
                .predicates
                .into_iter()
                .map(|p| p.import(module_id))
                .collect(),
            ty: self.ty.import(module_id),
        }
    }

    pub fn new(foralls: IndexSet<ForAll>, predicates: Vec<Predicate>, ty: Ty) -> Self {
        Self {
            foralls,
            predicates,
            ty,
        }
    }

    fn track_existing_ty_instantiation(
        &self,
        id: NodeID,
        param: Symbol,
        meta: crate::types::infer_ty::MetaVarId,
        session: &mut TypeSession,
    ) {
        session.track_ty_instantiation(
            id,
            param,
            Ty::Var {
                id: meta,
                level: Level(1),
            },
        );
    }

    fn fresh_ty_instantiation(
        &self,
        id: NodeID,
        param: Symbol,
        level: Level,
        tracked_level: Level,
        session: &mut TypeSession,
        substitutions: &mut InstantiationSubstitutions,
    ) -> Ty {
        let Ty::Var { id: meta, .. } = session.new_ty_meta_var(level) else {
            unreachable!()
        };

        let bounds = self.bounds_for(&param);
        tracing::debug!("instantiating {param:?} with {meta:?}, bounds: {bounds:?}");
        session
            .reverse_instantiations
            .ty
            .insert(meta, Ty::Param(param, bounds));
        substitutions.insert_ty(id, param, meta);

        let ty = Ty::Var {
            id: meta,
            level: tracked_level,
        };
        session.track_ty_instantiation(id, param, ty.clone());
        ty
    }

    fn fresh_row_instantiation(
        &self,
        id: NodeID,
        param: RowParamId,
        level: Level,
        session: &mut TypeSession,
        substitutions: &mut InstantiationSubstitutions,
    ) {
        let Row::Var(meta) = session.new_row_meta_var(level) else {
            unreachable!()
        };
        tracing::trace!("instantiating {param:?} with {meta:?}");
        substitutions.insert_row(id, param, meta);
        session.reverse_instantiations.row.insert(meta, param);
        session.track_row_instantiation(id, param, Row::Var(meta));
    }

    fn instantiate_predicates(
        &self,
        id: NodeID,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
    ) {
        for predicate in &self.predicates {
            predicate.instantiate(id, constraints, context);
        }
    }

    #[instrument(skip(self, session, context, constraints), ret)]
    pub(super) fn instantiate(
        &self,
        id: NodeID,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> Ty {
        tracing::debug!(
            "Scheme::instantiate - foralls: {:?}, predicates: {:?}, ty: {:?}",
            self.foralls,
            self.predicates,
            self.ty
        );
        let level = context.level();
        for forall in &self.foralls {
            match forall {
                ForAll::Ty(param) => {
                    if let Some(meta) = context.instantiations_mut().get_ty(&id, param).copied() {
                        self.track_existing_ty_instantiation(id, *param, meta, session);
                    } else {
                        self.fresh_ty_instantiation(
                            id,
                            *param,
                            level,
                            level,
                            session,
                            context.instantiations_mut(),
                        );
                    }
                }
                ForAll::Row(param) => {
                    if context.instantiations_mut().get_row(&id, param).is_none() {
                        self.fresh_row_instantiation(
                            id,
                            *param,
                            level,
                            session,
                            context.instantiations_mut(),
                        );
                    }
                }
            };
        }

        self.instantiate_predicates(id, constraints, context);

        tracing::trace!(
            "solver_instantiate ret subs: {:?}",
            context.instantiations_mut()
        );

        instantiate_ty(id, self.ty.clone(), context.instantiations_mut(), level)
    }

    #[instrument(skip(self, session, context, constraints,))]
    pub fn instantiate_with_args(
        &self,
        id: NodeID,
        args: &[(Ty, NodeID)],
        session: &mut TypeSession,
        context: &mut SolveContext,
        constraints: &mut ConstraintStore,
    ) -> (Ty, InstantiationSubstitutions) {
        let mut substitutions = InstantiationSubstitutions::default();
        let (ty_foralls, row_foralls): (Vec<ForAll>, Vec<ForAll>) = self
            .foralls
            .iter()
            .partition(|fa| matches!(fa, ForAll::Ty(_)));

        // We used to zip these with ty_foralls but that failed when the counts were different.
        let mut args = args.iter().rev().collect_vec();
        let group = context.group_info();

        for param in ty_foralls.iter() {
            let ForAll::Ty(param) = param else {
                unreachable!()
            };

            let ty = self.fresh_ty_instantiation(
                id,
                *param,
                context.level(),
                Level(1),
                session,
                &mut substitutions,
            );

            if let Some((arg_ty, arg_id)) = args.pop() {
                constraints.wants_equals_at(*arg_id, ty, arg_ty.clone(), &group);
            };
        }

        for row_forall in row_foralls {
            let ForAll::Row(row_param) = row_forall else {
                unreachable!();
            };

            self.fresh_row_instantiation(
                id,
                row_param,
                context.level(),
                session,
                &mut substitutions,
            );
        }

        self.instantiate_predicates(id, constraints, context);

        (
            instantiate_ty(id, self.ty.clone(), &substitutions, context.level()),
            substitutions,
        )
    }
}
