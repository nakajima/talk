use crate::{
    label::Label,
    name_resolution::symbol::{AssociatedTypeId, ProtocolId},
    span::Span,
    types::{
        constraints::{
            associated_equals::AssociatedEquals,
            call::Call,
            constraint::{Constraint, ConstraintCause},
            has_field::HasField,
            member::Member,
            type_member::TypeMember,
        },
        row::{Row, RowParamId},
        ty::{Level, Ty},
        type_operations::{
            InstantiationSubstitutions, apply_mult, instantiate_row, instantiate_ty,
        },
    },
};

// Predicates are kinda like Constraint templates. They ride around with schemes and get instantiated
// into constraints when the scheme itself is instantiated.
#[derive(Clone, PartialEq)]
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
    TypeMember {
        base: Ty,
        member: Label,
        returns: Ty,
        generics: Vec<Ty>,
    },
    AssociatedEquals {
        subject: Ty,             // the type the associated type is relative to
        protocol_id: ProtocolId, // protocol that declares the associated type
        associated_type_id: AssociatedTypeId,
        output: Ty, // a type variable (or any Ty) that must equal the witness
    },
}

impl Predicate {
    pub fn apply_substitutions(
        &self,
        substitutions: &mut crate::types::type_operations::UnificationSubstitutions,
    ) -> Self {
        use crate::types::type_operations::apply;

        match self {
            Self::HasField { row, label, ty } => Self::HasField {
                row: *row,
                label: label.clone(),
                ty: apply(ty.clone(), substitutions),
            },
            Self::Member {
                receiver,
                label,
                ty,
            } => Self::Member {
                receiver: apply(receiver.clone(), substitutions),
                label: label.clone(),
                ty: apply(ty.clone(), substitutions),
            },
            Self::TypeMember {
                base: owner,
                member,
                returns,
                generics,
            } => Self::TypeMember {
                base: apply(owner.clone(), substitutions),
                member: member.clone(),
                returns: apply(returns.clone(), substitutions),
                generics: apply_mult(generics.clone(), substitutions),
            },
            Self::Call {
                callee,
                args,
                returns,
                receiver,
            } => Self::Call {
                callee: apply(callee.clone(), substitutions),
                args: args
                    .iter()
                    .map(|arg| apply(arg.clone(), substitutions))
                    .collect(),
                returns: apply(returns.clone(), substitutions),
                receiver: receiver.as_ref().map(|r| apply(r.clone(), substitutions)),
            },
            Self::AssociatedEquals {
                subject,
                protocol_id,
                associated_type_id,
                output,
            } => Self::AssociatedEquals {
                subject: apply(subject.clone(), substitutions),
                protocol_id: *protocol_id,
                associated_type_id: *associated_type_id,
                output: apply(output.clone(), substitutions),
            },
        }
    }

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
            Self::TypeMember {
                base,
                member,
                returns,
                generics,
            } => Constraint::TypeMember(TypeMember {
                base: instantiate_ty(base, substitutions, level),
                name: member,
                generics: generics
                    .iter()
                    .map(|g| instantiate_ty(g.clone(), substitutions, level))
                    .collect(),
                result: instantiate_ty(returns, substitutions, level),
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

impl std::fmt::Debug for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::HasField { row, label, ty } => {
                write!(f, "*hasfield({label}: {ty:?}, {row:?})")
            }
            Predicate::Member {
                receiver,
                label,
                ty,
            } => {
                write!(f, "*member({receiver:?}.{label} = {ty:?})")
            }
            Predicate::Call {
                callee,
                args,
                returns,
                receiver,
            } => write!(
                f,
                "*call({}{callee:?}({args:?}) = {returns:?})",
                if let Some(rec) = receiver {
                    format!("{rec:?}")
                } else {
                    "".to_string()
                },
            ),
            Predicate::TypeMember {
                base,
                member,
                returns,
                generics,
            } => {
                write!(
                    f,
                    "*typemember({base:?}.{member}<{generics:?}> = {returns:?})"
                )
            }
            Predicate::AssociatedEquals {
                subject,
                protocol_id,
                associated_type_id,
                output,
            } => write!(
                f,
                "*associatedequals({subject:?}, {protocol_id:?}, {associated_type_id:?} = {output:?})"
            ),
        }
    }
}
