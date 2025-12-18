use indexmap::IndexSet;
use itertools::Itertools;
use tracing::instrument;

use crate::{
    compiling::module::ModuleId,
    node_id::NodeID,
    types::{
        constraints::store::ConstraintStore,
        infer_row::{InferRow, RowParamId},
        infer_ty::{InferTy, Level, TypeParamId},
        predicate::Predicate,
        solve_context::Solve,
        term_environment::EnvEntry,
        ty::{SomeType, Ty},
        type_operations::{InstantiationSubstitutions, instantiate_ty},
        type_session::TypeSession,
    },
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ForAll {
    Ty(TypeParamId),
    Row(RowParamId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scheme<T: SomeType> {
    pub(crate) foralls: IndexSet<ForAll>,
    pub(crate) predicates: Vec<Predicate<T>>,
    pub(crate) ty: T,
}

impl Scheme<Ty> {
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
}

impl<T: SomeType> std::hash::Hash for Scheme<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ty.hash(state);
        for forall in self.foralls.iter() {
            forall.hash(state);
        }
    }
}

impl<T: SomeType> SomeType for EnvEntry<T> {
    type RowType = InferRow;

    fn void() -> Self {
        EnvEntry::Mono(T::void())
    }

    fn contains_var(&self) -> bool {
        match self {
            Self::Mono(ty) => ty.contains_var(),
            Self::Scheme(scheme) => scheme.ty.contains_var(),
        }
    }
}

impl Scheme<InferTy> {
    pub fn new(
        foralls: IndexSet<ForAll>,
        predicates: Vec<Predicate<InferTy>>,
        ty: InferTy,
    ) -> Self {
        Self {
            foralls,
            predicates,
            ty,
        }
    }
}

impl Scheme<Ty> {
    pub fn new(foralls: IndexSet<ForAll>, predicates: Vec<Predicate<Ty>>, ty: Ty) -> Self {
        assert!(
            !ty.contains_var(),
            "Scheme ty cannot contain type/row meta vars: {ty:?}"
        );

        Self {
            foralls,
            predicates,
            ty,
        }
    }
}

impl Scheme<InferTy> {
    #[instrument(skip(self, session, context, constraints), ret)]
    pub(super) fn instantiate(
        &self,
        id: NodeID,
        constraints: &mut ConstraintStore,
        context: &mut impl Solve,
        session: &mut TypeSession,
    ) -> InferTy {
        let level = context.level();
        for forall in &self.foralls {
            match forall {
                ForAll::Ty(param) => {
                    if let Some(meta) = context.instantiations_mut().get_ty(&id, param) {
                        session.type_catalog.instantiations.ty.insert(
                            (id, *param),
                            InferTy::Var {
                                id: *meta,
                                level: Level(1),
                            },
                        );

                        continue;
                    }

                    let InferTy::Var { id: meta, .. } = session.new_ty_meta_var(level) else {
                        unreachable!()
                    };

                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    session.reverse_instantiations.ty.insert(meta, *param);
                    context.instantiations_mut().insert_ty(id, *param, meta);

                    session
                        .type_catalog
                        .instantiations
                        .ty
                        .insert((id, *param), InferTy::Var { id: meta, level });
                }
                ForAll::Row(param) => {
                    if context.instantiations_mut().get_row(&id, param).is_some() {
                        continue;
                    }

                    let InferRow::Var(meta) = session.new_row_meta_var(level) else {
                        unreachable!()
                    };
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    context.instantiations_mut().insert_row(id, *param, meta);
                    session.reverse_instantiations.row.insert(meta, *param);
                    session
                        .type_catalog
                        .instantiations
                        .row
                        .insert((id, *param), InferRow::Var(meta));
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
        args: &[(InferTy, NodeID)],
        session: &mut TypeSession,
        context: &mut impl Solve,
        constraints: &mut ConstraintStore,
    ) -> (InferTy, InstantiationSubstitutions) {
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

            let ty @ InferTy::Var { id: meta_var, .. } = session.new_ty_meta_var(context.level())
            else {
                unreachable!();
            };

            session.reverse_instantiations.ty.insert(meta_var, *param);

            if let Some((arg_ty, _id)) = args.pop() {
                constraints.wants_equals(ty.clone(), arg_ty.clone());
            };

            substitutions.insert_ty(id, *param, meta_var);
            session.type_catalog.instantiations.ty.insert(
                (id, *param),
                InferTy::Var {
                    id: meta_var,
                    level: Level(1),
                },
            );
        }

        for row_forall in row_foralls {
            let ForAll::Row(row_param) = row_forall else {
                unreachable!();
            };

            let InferRow::Var(row_meta) = session.new_row_meta_var(context.level()) else {
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
                .row
                .insert((id, row_param), InferRow::Var(row_meta));
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
