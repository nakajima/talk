use indexmap::IndexSet;
use itertools::Itertools;
use tracing::instrument;

use crate::{
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::{InferRow, RowParamId},
        infer_ty::{InferTy, Level, TypeParamId},
        predicate::Predicate,
        solve_context::Solve,
        term_environment::EnvEntry,
        ty::{SomeType, Ty},
        type_operations::{InstantiationSubstitutions, instantiate_ty},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ForAll {
    Ty(TypeParamId),
    Row(RowParamId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Scheme<T: SomeType> {
    pub(crate) foralls: IndexSet<ForAll>,
    pub(super) predicates: Vec<Predicate<T>>,
    pub(crate) ty: T,
}

impl<T: SomeType> SomeType for EnvEntry<T> {
    type RowType = InferRow;

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
    #[instrument(skip(self, session, context), ret)]
    pub(super) fn instantiate(
        &self,
        id: NodeID,
        context: &mut impl Solve,
        session: &mut TypeSession,
        span: Span,
    ) -> InferTy {
        let level = context.level();
        for forall in &self.foralls {
            match forall {
                ForAll::Ty(param) => {
                    if context.instantiations_mut().ty.contains_key(param) {
                        continue;
                    }

                    let InferTy::Var { id: meta, .. } = session.new_ty_meta_var(level) else {
                        unreachable!()
                    };

                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    session.reverse_instantiations.ty.insert(meta, *param);
                    context.instantiations_mut().ty.insert(*param, meta);
                    session
                        .type_catalog
                        .instantiations
                        .ty
                        .insert((id, *param), InferTy::Var { id: meta, level });
                }
                ForAll::Row(param) => {
                    if context.instantiations_mut().row.contains_key(param) {
                        continue;
                    }

                    let InferRow::Var(meta) = session.new_row_meta_var(level) else {
                        unreachable!()
                    };
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    context.instantiations_mut().row.insert(*param, meta);
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
            let constraint = predicate.instantiate(id, context.instantiations_mut(), span, level);
            tracing::trace!("predicate instantiated: {predicate:?} -> {constraint:?}");
            context.wants_mut().push(constraint);
        }

        tracing::trace!(
            "solver_instantiate ret subs: {:?}",
            context.instantiations_mut()
        );

        instantiate_ty(self.ty.clone(), context.instantiations_mut(), level)
    }

    #[instrument(skip(self, session, level, wants, span))]
    pub fn instantiate_with_args(
        &self,
        id: NodeID,
        args: &[(InferTy, NodeID)],
        session: &mut TypeSession,
        level: Level,
        wants: &mut Wants,
        span: Span,
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

            let ty @ InferTy::Var { id: meta_var, .. } = session.new_ty_meta_var(level) else {
                unreachable!();
            };

            session.reverse_instantiations.ty.insert(meta_var, *param);

            if let Some((arg_ty, id)) = args.pop() {
                wants.equals(
                    ty.clone(),
                    arg_ty.clone(),
                    ConstraintCause::CallTypeArg(*id),
                    span,
                );
            }

            substitutions.ty.insert(*param, meta_var);
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

            let InferRow::Var(row_meta) = session.new_row_meta_var(level) else {
                unreachable!()
            };
            substitutions.row.insert(row_param, row_meta);
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
            let constraint = predicate.instantiate(id, &substitutions, span, level);
            tracing::trace!("predicate instantiated: {predicate:?} -> {constraint:?}");
            wants.push(constraint);
        }

        (
            instantiate_ty(self.ty.clone(), &substitutions, level),
            substitutions,
        )
    }
}
