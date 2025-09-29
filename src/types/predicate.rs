use crate::{
    label::Label,
    name_resolution::symbol::{AssociatedTypeId, TypeId},
    span::Span,
    types::{
        constraints::{
            associated_equals::AssociatedEquals,
            call::Call,
            constraint::{Constraint, ConstraintCause},
            has_field::HasField,
            member::Member,
        },
        row::{Row, RowParamId},
        ty::{Level, Ty},
        type_operations::{InstantiationSubstitutions, instantiate_row, instantiate_ty},
    },
};

// Predicates are kinda like Constraint templates. They ride around with schemes and get instantiated
// into constraints when the scheme itself is instantiated.
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
    AssociatedEquals {
        subject: Ty,         // the type the associated type is relative to
        protocol_id: TypeId, // protocol that declares the associated type
        associated_type_id: AssociatedTypeId,
        output: Ty, // a type variable (or any Ty) that must equal the witness
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
            Self::AssociatedEquals {
                subject,
                protocol_id,
                associated_type_id,
                output,
            } => Constraint::AssociatedEquals(AssociatedEquals {
                subject: instantiate_ty(subject, substitutions, level),
                protocol_id,
                associated_type_id,
                output: instantiate_ty(output, substitutions, level),
                span,
                cause: ConstraintCause::Internal,
            }),
        }
    }
}
