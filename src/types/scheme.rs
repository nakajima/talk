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
        type_args::{Instantiated, TypeArgs},
        type_session::{MetaOrigin, TypeSession},
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

    fn fresh_ty_instantiation(
        &self,
        param: Symbol,
        level: Level,
        session: &mut TypeSession,
        type_args: &mut TypeArgs,
    ) -> Ty {
        let bounds = self.bounds_for(&param);
        let Ty::Var { id: meta, .. } = session.new_ty_meta_var_with_origin(
            level,
            Some(MetaOrigin::TypeParam {
                param,
                bounds: bounds.clone(),
            }),
        ) else {
            unreachable!()
        };

        tracing::debug!("instantiating {param:?} with {meta:?}, bounds: {bounds:?}");

        let ty = Ty::Var { id: meta, level };
        type_args.ty.insert(param, ty.clone());
        ty
    }

    fn fresh_row_instantiation(
        &self,
        param: RowParamId,
        level: Level,
        session: &mut TypeSession,
        type_args: &mut TypeArgs,
    ) {
        let row = session.new_row_meta_var_with_origin(level, Some(MetaOrigin::RowParam { param }));
        tracing::trace!("instantiating {param:?} with {row:?}");
        if let Row::Var(meta) = row {
            type_args.row.insert(param, Row::Var(meta));
        }
    }

    #[instrument(skip(self, session, context, constraints), ret)]
    pub(super) fn instantiate(
        &self,
        id: NodeID,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> Instantiated<Ty> {
        tracing::debug!(
            "Scheme::instantiate - foralls: {:?}, predicates: {:?}, ty: {:?}",
            self.foralls,
            self.predicates,
            self.ty
        );
        let level = context.level();
        let mut type_args = TypeArgs::default();
        for forall in &self.foralls {
            match forall {
                ForAll::Ty(param) => {
                    self.fresh_ty_instantiation(*param, level, session, &mut type_args);
                }
                ForAll::Row(param) => {
                    self.fresh_row_instantiation(*param, level, session, &mut type_args);
                }
            };
        }

        for predicate in &self.predicates {
            predicate.instantiate(id, &type_args, constraints, context);
        }

        tracing::trace!("solver_instantiate ret type args: {:?}", type_args);

        Instantiated::new(type_args.apply(self.ty.clone()), type_args)
    }

    fn explicit_ty_arg_count(&self) -> usize {
        self.foralls
            .iter()
            .filter(|forall| matches!(forall, ForAll::Ty(_)))
            .count()
    }

    fn validate_explicit_type_args(
        &self,
        args: &[(Ty, NodeID)],
    ) -> Result<(), crate::types::type_error::TypeError> {
        if args.is_empty() {
            return Ok(());
        }

        let expected = self.explicit_ty_arg_count();
        if args.len() != expected {
            return Err(crate::types::type_error::TypeError::GenericArgCount {
                expected: expected as u8,
                actual: args.len() as u8,
            });
        }

        Ok(())
    }

    #[instrument(skip(self, session, context, constraints,))]
    pub fn instantiate_with_checked_args(
        &self,
        id: NodeID,
        args: &[(Ty, NodeID)],
        session: &mut TypeSession,
        context: &mut SolveContext,
        constraints: &mut ConstraintStore,
    ) -> Result<Instantiated<Ty>, crate::types::type_error::TypeError> {
        self.validate_explicit_type_args(args)?;
        Ok(self.instantiate_with_args(id, args, session, context, constraints))
    }

    #[instrument(skip(self, session, context, constraints,))]
    pub fn instantiate_with_args(
        &self,
        id: NodeID,
        args: &[(Ty, NodeID)],
        session: &mut TypeSession,
        context: &mut SolveContext,
        constraints: &mut ConstraintStore,
    ) -> Instantiated<Ty> {
        let mut type_args = TypeArgs::default();
        let (ty_foralls, row_foralls): (Vec<ForAll>, Vec<ForAll>) = self
            .foralls
            .iter()
            .partition(|fa| matches!(fa, ForAll::Ty(_)));

        let mut args = args.iter().rev().collect_vec();
        let group = context.group_info();

        for param in ty_foralls.iter() {
            let ForAll::Ty(param) = param else {
                unreachable!()
            };

            let ty = self.fresh_ty_instantiation(*param, context.level(), session, &mut type_args);

            if let Some((arg_ty, arg_id)) = args.pop() {
                constraints.wants_equals_at(*arg_id, ty, arg_ty.clone(), &group);
            };
        }

        for row_forall in row_foralls {
            let ForAll::Row(row_param) = row_forall else {
                unreachable!();
            };

            self.fresh_row_instantiation(row_param, context.level(), session, &mut type_args);
        }

        for predicate in &self.predicates {
            predicate.instantiate(id, &type_args, constraints, context);
        }

        Instantiated::new(type_args.apply(self.ty.clone()), type_args)
    }
}
