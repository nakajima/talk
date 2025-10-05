use rustc_hash::FxHashMap;

use crate::{
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::{InferRow, RowParamId},
        infer_ty::{InferTy, Level, TypeParamId},
        passes::{dependencies_pass::ConformanceRequirement, inference_pass::Meta},
        predicate::Predicate,
        term_environment::EnvEntry,
        ty::{SomeType, Ty},
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, instantiate_ty, substitute,
        },
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ForAll {
    Ty(TypeParamId),
    Row(RowParamId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Scheme<T: SomeType> {
    pub(super) foralls: Vec<ForAll>,
    pub(super) predicates: Vec<Predicate<T>>,
    pub(super) ty: T,
}

impl Scheme<InferTy> {
    pub fn new(foralls: Vec<ForAll>, predicates: Vec<Predicate<InferTy>>, ty: InferTy) -> Self {
        Self {
            foralls,
            predicates,
            ty,
        }
    }
}

impl Scheme<Ty> {
    pub fn new(foralls: Vec<ForAll>, predicates: Vec<Predicate<Ty>>, ty: Ty) -> Self {
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
    pub fn inference_instantiate(
        &self,
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
                    let InferTy::UnificationVar { id: meta, .. } = session.new_ty_meta_var(level)
                    else {
                        unreachable!()
                    };
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    substitutions.ty.insert(*param, meta);

                    if let Some(bounds) = session.type_param_bounds.get(param).cloned() {
                        for bound in bounds {
                            let protocol = session
                                .type_catalog
                                .protocols
                                .get(&bound.protocol_id)
                                .cloned()
                                .expect("didn't get protocol bound");

                            let mut substitutions = FxHashMap::default();
                            substitutions.insert(
                                InferTy::Param(*param),
                                InferTy::UnificationVar { id: meta, level },
                            );

                            for (label, requirement) in &protocol.requirements {
                                tracing::trace!("adding {label} requirement to {meta:?}");

                                let ConformanceRequirement::Unfulfilled(sym) = requirement else {
                                    unreachable!(
                                        "protocol.requirements must always be unfulfilled"
                                    );
                                };

                                let entry =
                                    session.lookup(sym).expect("didn't get requirement entry");

                                let ty = match entry {
                                    EnvEntry::Mono(ty) => ty.clone(),
                                    EnvEntry::Scheme(scheme) => scheme.ty.clone(),
                                };

                                wants.member(
                                    InferTy::UnificationVar { id: meta, level },
                                    label.clone(),
                                    substitute(ty, &substitutions),
                                    ConstraintCause::Internal,
                                    span,
                                );
                            }
                        }
                    }
                }
                ForAll::Row(param) => {
                    let InferRow::Var(meta) = session.new_row_meta_var(level) else {
                        unreachable!()
                    };
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    substitutions.row.insert(*param, meta);
                }
            };
        }

        for predicate in &self.predicates {
            let constraint = predicate.instantiate(&substitutions, span, level);
            tracing::trace!("predicate instantiated: {predicate:?} -> {constraint:?}");
            wants.push(constraint);
        }

        (
            instantiate_ty(self.ty.clone(), &substitutions, level),
            substitutions,
        )
    }

    // Used while solving
    pub fn solver_instantiate(
        &self,
        session: &mut TypeSession,
        level: Level,
        wants: &mut Wants,
        span: Span,
        unification_substitutions: &mut UnificationSubstitutions,
    ) -> (InferTy, InstantiationSubstitutions) {
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = InstantiationSubstitutions::default();

        for forall in &self.foralls {
            match forall {
                ForAll::Ty(param) => {
                    let InferTy::UnificationVar { id: meta, .. } = session.new_ty_meta_var(level)
                    else {
                        unreachable!()
                    };

                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    unification_substitutions
                        .meta_levels
                        .insert(Meta::Ty(meta), level);
                    substitutions.ty.insert(*param, meta);
                }
                ForAll::Row(param) => {
                    let InferRow::Var(meta) = session.new_row_meta_var(level) else {
                        unreachable!()
                    };
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    unification_substitutions
                        .meta_levels
                        .insert(Meta::Row(meta), level);
                    substitutions.row.insert(*param, meta);
                }
            };
        }

        for predicate in &self.predicates {
            let constraint = predicate.instantiate(&substitutions, span, level);
            tracing::trace!("predicate instantiated: {predicate:?} -> {constraint:?}");
            wants.push(constraint);
        }

        tracing::trace!("solver_instantiate ret subs: {substitutions:?}");

        (
            instantiate_ty(self.ty.clone(), &substitutions, level),
            substitutions,
        )
    }

    pub fn instantiate_with_args(
        &self,
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

            let ty @ InferTy::UnificationVar { id: meta_var, .. } = session.new_ty_meta_var(level)
            else {
                unreachable!();
            };

            wants.equals(
                ty.clone(),
                arg_ty.clone(),
                ConstraintCause::CallTypeArg(*id),
                span,
            );

            substitutions.ty.insert(*param, meta_var);
        }

        for row_forall in row_foralls {
            let ForAll::Row(row_param) = row_forall else {
                unreachable!();
            };

            let InferRow::Var(row_meta) = session.new_row_meta_var(level) else {
                unreachable!()
            };
            substitutions.row.insert(row_param, row_meta);
        }

        for predicate in &self.predicates {
            let constraint = predicate.instantiate(&substitutions, span, level);
            tracing::trace!("predicate instantiated: {predicate:?} -> {constraint:?}");
            wants.push(constraint);
        }

        instantiate_ty(self.ty.clone(), &substitutions, level)
    }
}
