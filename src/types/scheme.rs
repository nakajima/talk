use derive_visitor::{Drive, DriveMut};
use indexmap::IndexSet;
use itertools::Itertools;
use tracing::instrument;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
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
                    if let Some(meta) = context.instantiations_mut().get_ty(&id, param) {
                        session.type_catalog.instantiations.insert_ty(
                            id,
                            *param,
                            Ty::Var {
                                id: *meta,
                                level: Level(1),
                            },
                        );

                        continue;
                    }

                    let Ty::Var { id: meta, .. } = session.new_ty_meta_var(level) else {
                        unreachable!()
                    };

                    // Collect protocol bounds for this param from the scheme's predicates
                    let bounds: Vec<_> = self
                        .predicates
                        .iter()
                        .filter_map(|pred| {
                            if let Predicate::Conforms {
                                param: p,
                                protocol_id,
                                ..
                            } = pred
                            {
                                if p == param { Some(*protocol_id) } else { None }
                            } else {
                                None
                            }
                        })
                        .collect();

                    tracing::debug!("instantiating {param:?} with {meta:?}, bounds: {bounds:?}");
                    session
                        .reverse_instantiations
                        .ty
                        .insert(meta, Ty::Param(*param, bounds));
                    context.instantiations_mut().insert_ty(id, *param, meta);

                    session.type_catalog.instantiations.insert_ty(
                        id,
                        *param,
                        Ty::Var { id: meta, level },
                    );
                }
                ForAll::Row(param) => {
                    if context.instantiations_mut().get_row(&id, param).is_some() {
                        continue;
                    }

                    let Row::Var(meta) = session.new_row_meta_var(level) else {
                        unreachable!()
                    };
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    context.instantiations_mut().insert_row(id, *param, meta);
                    session.reverse_instantiations.row.insert(meta, *param);
                    session
                        .type_catalog
                        .instantiations
                        .insert_row(id, *param, Row::Var(meta));
                }
            };
        }

        for predicate in &self.predicates {
            predicate.instantiate(id, constraints, context);
        }

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
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = InstantiationSubstitutions::default();
        let (ty_foralls, row_foralls): (Vec<ForAll>, Vec<ForAll>) = self
            .foralls
            .iter()
            .partition(|fa| matches!(fa, ForAll::Ty(_)));

        // We used to zip these with ty_foralls but that failed when the counts were different.
        let mut args = args.iter().rev().collect_vec();

        for param in ty_foralls.iter() {
            let ForAll::Ty(param) = param else {
                unreachable!()
            };

            let ty @ Ty::Var { id: meta_var, .. } = session.new_ty_meta_var(context.level()) else {
                unreachable!();
            };

            // Collect protocol bounds for this param from the scheme's predicates
            let bounds: Vec<_> = self
                .predicates
                .iter()
                .filter_map(|pred| {
                    if let Predicate::Conforms {
                        param: p,
                        protocol_id,
                        ..
                    } = pred
                    {
                        if p == param { Some(*protocol_id) } else { None }
                    } else {
                        None
                    }
                })
                .collect();

            session
                .reverse_instantiations
                .ty
                .insert(meta_var, Ty::Param(*param, bounds));

            if let Some((arg_ty, arg_id)) = args.pop() {
                constraints.wants_equals_at(
                    *arg_id,
                    ty.clone(),
                    arg_ty.clone(),
                    &context.group_info(),
                );
            };

            substitutions.insert_ty(id, *param, meta_var);
            session.type_catalog.instantiations.insert_ty(
                id,
                *param,
                Ty::Var {
                    id: meta_var,
                    level: Level(1),
                },
            );
        }

        for row_forall in row_foralls {
            let ForAll::Row(row_param) = row_forall else {
                unreachable!();
            };

            let Row::Var(row_meta) = session.new_row_meta_var(context.level()) else {
                unreachable!()
            };
            substitutions.insert_row(id, row_param, row_meta);
            session
                .reverse_instantiations
                .row
                .insert(row_meta, row_param);
            session
                .type_catalog
                .instantiations
                .insert_row(id, row_param, Row::Var(row_meta));
        }

        for predicate in &self.predicates {
            predicate.instantiate(id, constraints, context);
        }

        (
            instantiate_ty(id, self.ty.clone(), &substitutions, context.level()),
            substitutions,
        )
    }
}
