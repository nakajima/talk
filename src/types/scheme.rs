use indexmap::IndexSet;
use tracing::instrument;

use crate::{
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::{InferRow, RowParamId},
        infer_ty::{InferTy, Level, TypeParamId},
        predicate::Predicate,
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

impl SomeType for EnvEntry {
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
    // Used while solving
    #[instrument(skip(self, session, level, wants, span,))]
    pub fn instantiate(
        &self,
        id: NodeID,
        session: &mut TypeSession,
        level: Level,
        wants: &mut Wants,
        span: Span,
    ) -> (InferTy, InstantiationSubstitutions) {
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = InstantiationSubstitutions::default();

        for forall in &self.foralls {
            match forall {
                ForAll::Ty(param) => {
                    let InferTy::Var { id: meta, .. } = session.new_ty_meta_var(level) else {
                        unreachable!()
                    };

                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    session.reverse_instantiations.ty.insert(meta, *param);
                    substitutions.ty.insert(*param, meta);
                    session
                        .type_catalog
                        .instantiations
                        .ty
                        .insert((id, *param), InferTy::Var { id: meta, level });
                }
                ForAll::Row(param) => {
                    let InferRow::Var(meta) = session.new_row_meta_var(level) else {
                        unreachable!()
                    };
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    substitutions.row.insert(*param, meta);
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
            let constraint = predicate.instantiate(id, &substitutions, span, level);
            tracing::trace!("predicate instantiated: {predicate:?} -> {constraint:?}");
            wants.push(constraint);
        }

        tracing::trace!("solver_instantiate ret subs: {substitutions:?}");

        (
            instantiate_ty(self.ty.clone(), &substitutions, level),
            substitutions,
        )
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
    ) -> InferTy {
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = InstantiationSubstitutions::default();
        let (ty_foralls, row_foralls): (Vec<ForAll>, Vec<ForAll>) = self
            .foralls
            .iter()
            .partition(|fa| matches!(fa, ForAll::Ty(_)));

        for (param, (arg_ty, id)) in ty_foralls.iter().zip(args) {
            let ForAll::Ty(param) = param else {
                unreachable!()
            };

            let ty @ InferTy::Var { id: meta_var, .. } = session.new_ty_meta_var(level) else {
                unreachable!();
            };

            session.reverse_instantiations.ty.insert(meta_var, *param);

            wants.equals(
                ty.clone(),
                arg_ty.clone(),
                ConstraintCause::CallTypeArg(*id),
                span,
            );

            substitutions.ty.insert(*param, meta_var);
            session.type_catalog.instantiations.ty.insert(
                (*id, *param),
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

        instantiate_ty(self.ty.clone(), &substitutions, level)
    }
}
