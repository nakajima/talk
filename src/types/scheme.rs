use rustc_hash::{FxHashMap, FxHashSet};

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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ForAll {
    Ty(TypeParamId),
    Row(RowParamId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Scheme<T: SomeType> {
    pub(crate) foralls: FxHashSet<ForAll>,
    pub(super) predicates: Vec<Predicate<T>>,
    pub(crate) ty: T,
}

impl Scheme<InferTy> {
    pub fn new(
        foralls: FxHashSet<ForAll>,
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
    pub fn new(foralls: FxHashSet<ForAll>, predicates: Vec<Predicate<Ty>>, ty: Ty) -> Self {
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
                    let InferTy::UnificationVar { id: meta, .. } = session.new_ty_meta_var(level)
                    else {
                        unreachable!()
                    };
                    session.reverse_instantiations.ty.insert(meta, *param);
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    substitutions.ty.insert(*param, meta);
                    session
                        .type_catalog
                        .instantiations
                        .ty
                        .insert((id, *param), InferTy::UnificationVar { id: meta, level });

                    if let Some(bounds) = session.type_param_bounds.get(param).cloned() {
                        for bound in bounds {
                            let protocol = session
                                .lookup_protocol(bound.protocol_id)
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
                                    id,
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

        (
            instantiate_ty(self.ty.clone(), &substitutions, level),
            substitutions,
        )
    }

    // Used while solving
    pub fn solver_instantiate(
        &self,
        id: NodeID,
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
                    session.reverse_instantiations.ty.insert(meta, *param);
                    unification_substitutions
                        .meta_levels
                        .insert(Meta::Ty(meta), level);
                    substitutions.ty.insert(*param, meta);
                    session
                        .type_catalog
                        .instantiations
                        .ty
                        .insert((id, *param), InferTy::UnificationVar { id: meta, level });
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

            let ty @ InferTy::UnificationVar { id: meta_var, .. } = session.new_ty_meta_var(level)
            else {
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
                InferTy::UnificationVar {
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
