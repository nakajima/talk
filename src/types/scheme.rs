use crate::{
    label::Label,
    node_kinds::type_annotation::TypeAnnotation,
    span::Span,
    types::{
        constraints::{Constraint, ConstraintCause, HasField},
        passes::inference_pass::{InferencePass, Wants},
        row::{Row, RowParamId},
        ty::{Level, Ty, TypeParamId},
        type_operations::{InstantiationSubstitutions, instantiate_row, instantiate_ty},
    },
};

#[derive(Debug, Copy, Clone)]
pub enum ForAll {
    Ty(TypeParamId),
    Row(RowParamId),
}

#[derive(Debug, Clone)]
pub enum Predicate {
    HasField {
        row: RowParamId,
        label: Label,
        ty: Ty,
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
        }
    }
}

#[derive(Debug, Clone)]
pub struct Scheme {
    foralls: Vec<ForAll>,
    predicates: Vec<Predicate>,
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

    pub fn instantiate(
        &self,
        pass: &mut InferencePass,
        level: Level,
        wants: &mut Wants,
        span: Span,
    ) -> Ty {
        // Map each quantified meta id to a fresh meta at this use-site level
        let mut substitutions = InstantiationSubstitutions::default();

        for forall in &self.foralls {
            match forall {
                ForAll::Ty(param) => {
                    let Ty::MetaVar { id: meta, .. } = pass.new_ty_meta_var(level) else {
                        unreachable!()
                    };
                    tracing::trace!("instantiating {param:?} with {meta:?}");
                    substitutions.ty.insert(*param, meta);
                }
                ForAll::Row(param) => {
                    let Ty::Record(box Row::Var(meta)) = pass.new_row_meta_var(level) else {
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

        instantiate_ty(self.ty.clone(), &substitutions, level)
    }

    pub fn instantiate_with_args(
        &self,
        args: &[TypeAnnotation],
        pass: &mut InferencePass,
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

        for (param, arg) in ty_foralls.iter().zip(args) {
            let ForAll::Ty(param) = param else {
                unreachable!()
            };

            let arg_ty = pass.infer_type_annotation(arg, level, wants);
            let ty @ Ty::MetaVar { id: meta_var, .. } = pass.new_ty_meta_var(level) else {
                unreachable!();
            };

            wants.equals(ty.clone(), arg_ty, ConstraintCause::CallTypeArg(arg.id));

            substitutions.ty.insert(*param, meta_var);
        }

        for row_forall in row_foralls {
            let ForAll::Row(row_param) = row_forall else {
                unreachable!();
            };

            let Ty::Record(box Row::Var(row_meta)) = pass.new_row_meta_var(level) else {
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
