use crate::{
    label::Label,
    node_id::NodeID,
    span::Span,
    types::{
        constraint::{Constraint, ConstraintCause},
        constraints::{call::Call, has_field::HasField, member::Member},
        passes::inference_pass::Meta,
        row::{Row, RowParamId},
        ty::{Level, Ty, TypeParamId},
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, instantiate_row, instantiate_ty,
        },
        type_session::{TypeSession, TypingPhase},
        wants::Wants,
    },
};

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ForAll {
    Ty(TypeParamId),
    Row(RowParamId),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Predicate {
    HasField {
        row: RowParamId,
        label: Label,
        ty: Ty,
    },
    Member {
        receiver: Ty,
        label: Label,
        ty: Ty,
    },
    Call {
        callee: Ty,
        args: Vec<Ty>,
        returns: Ty,
        receiver: Option<Ty>,
    },
}

impl Predicate {
    pub fn instantiate(
        &self,
        substitutions: &InstantiationSubstitutions,
        span: Span,
        level: Level,
    ) -> Constraint {
        match self.clone() {
            Self::HasField { row, label, ty } => Constraint::HasField(HasField {
                row: instantiate_row(Row::Param(row), substitutions, level),
                label,
                ty: instantiate_ty(ty, substitutions, level),
                cause: ConstraintCause::Internal,
                span,
            }),
            Self::Member {
                receiver,
                label,
                ty,
            } => Constraint::Member(Member {
                receiver: instantiate_ty(receiver, substitutions, level),
                label,
                ty: instantiate_ty(ty, substitutions, level),
                cause: ConstraintCause::Internal,
                span,
            }),
            Self::Call {
                callee,
                args,
                returns,
                receiver,
            } => Constraint::Call(Call {
                callee: instantiate_ty(callee, substitutions, level),
                args: args
                    .iter()
                    .map(|f| instantiate_ty(f.clone(), substitutions, level))
                    .collect(),
                returns: instantiate_ty(returns, substitutions, level),
                receiver: receiver.map(|r| instantiate_ty(r.clone(), substitutions, level)),
                span,
                cause: ConstraintCause::Internal,
            }),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Scheme {
    pub(super) foralls: Vec<ForAll>,
    pub(super) predicates: Vec<Predicate>,
    pub(super) ty: Ty,
}

impl Scheme {
    pub fn new(foralls: Vec<ForAll>, predicates: Vec<Predicate>, ty: Ty) -> Self {
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

    pub fn inference_instantiate<P: TypingPhase>(
        &self,
        session: &mut TypeSession<P>,
        level: Level,
        wants: &mut Wants,
        span: Span,
    ) -> (Ty, InstantiationSubstitutions) {
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = InstantiationSubstitutions::default();

        for forall in &self.foralls {
            match forall {
                ForAll::Ty(param) => {
                    let Ty::UnificationVar { id: meta, .. } = session.new_ty_meta_var(level) else {
                        unreachable!()
                    };
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    substitutions.ty.insert(*param, meta);
                }
                ForAll::Row(param) => {
                    let Row::Var(meta) = session.new_row_meta_var(level) else {
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
    pub fn solver_instantiate<P: TypingPhase>(
        &self,
        session: &mut TypeSession<P>,
        level: Level,
        wants: &mut Wants,
        span: Span,
        unification_substitutions: &mut UnificationSubstitutions,
    ) -> (Ty, InstantiationSubstitutions) {
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = InstantiationSubstitutions::default();

        for forall in &self.foralls {
            match forall {
                ForAll::Ty(param) => {
                    let Ty::UnificationVar { id: meta, .. } = session.new_ty_meta_var(level) else {
                        unreachable!()
                    };

                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    unification_substitutions
                        .meta_levels
                        .insert(Meta::Ty(meta), level);
                    substitutions.ty.insert(*param, meta);
                }
                ForAll::Row(param) => {
                    let Row::Var(meta) = session.new_row_meta_var(level) else {
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

    pub fn instantiate_with_args<P: TypingPhase>(
        &self,
        args: &[(Ty, NodeID)],
        session: &mut TypeSession<P>,
        level: Level,
        wants: &mut Wants,
        span: Span,
    ) -> Ty {
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

            let ty @ Ty::UnificationVar { id: meta_var, .. } = session.new_ty_meta_var(level)
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

            let Row::Var(row_meta) = session.new_row_meta_var(level) else {
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
