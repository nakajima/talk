use crate::{
    label::Label,
    name_resolution::symbol::ProtocolId,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::{
            call::Call,
            conforms::Conforms,
            constraint::{Constraint, ConstraintCause},
            equals::Equals,
            has_field::HasField,
            member::Member,
            projection::Projection,
            type_member::TypeMember,
        },
        infer_row::{InferRow, RowParamId},
        infer_ty::{InferTy, Level, TypeParamId},
        ty::{SomeType, Ty},
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, apply, apply_mult,
            instantiate_row, instantiate_ty,
        },
    },
};

// Predicates are kinda like Constraint templates. They ride around with schemes and get instantiated
// into constraints when the scheme itself is instantiated.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Predicate<T: SomeType> {
    HasField {
        row: RowParamId,
        label: Label,
        ty: T,
    },
    Projection {
        base: InferTy,
        label: Label,
        returns: InferTy,
    },
    Conforms {
        param: TypeParamId,
        protocol_id: ProtocolId,
        span: Span,
    },
    Member {
        receiver: T,
        label: Label,
        ty: T,
    },
    Equals {
        lhs: T,
        rhs: T,
    },
    Call {
        callee: T,
        args: Vec<T>,
        returns: T,
        receiver: Option<T>,
    },
    TypeMember {
        base: T,
        member: Label,
        returns: T,
        generics: Vec<T>,
    },
}

impl From<Predicate<InferTy>> for Predicate<Ty> {
    fn from(value: Predicate<InferTy>) -> Self {
        match value {
            Predicate::Projection {
                base,
                label,
                returns,
            } => Self::Projection {
                base,
                label,
                returns,
            },
            Predicate::<InferTy>::Conforms {
                param,
                protocol_id,
                span,
            } => Self::Conforms {
                param,
                protocol_id,
                span,
            },
            Predicate::<InferTy>::Equals { lhs, rhs } => Self::Equals {
                lhs: lhs.into(),
                rhs: rhs.into(),
            },
            Predicate::<InferTy>::HasField { row, label, ty } => Self::HasField {
                row,
                label,
                ty: ty.into(),
            },
            Predicate::<InferTy>::Member {
                receiver,
                label,
                ty,
            } => Self::Member {
                receiver: receiver.into(),
                label,
                ty: ty.into(),
            },
            Predicate::<InferTy>::TypeMember {
                base: owner,
                member,
                returns,
                generics,
            } => Self::TypeMember {
                base: owner.into(),
                member: member.clone(),
                returns: returns.into(),
                generics: generics.into_iter().map(|g| g.into()).collect(),
            },
            Predicate::<InferTy>::Call {
                callee,
                args,
                returns,
                receiver,
            } => Self::Call {
                callee: callee.into(),
                args: args.into_iter().map(|arg| arg.into()).collect(),
                returns: returns.into(),
                receiver: receiver.map(|r| r.into()),
            },
        }
    }
}

impl From<Predicate<Ty>> for Predicate<InferTy> {
    fn from(value: Predicate<Ty>) -> Self {
        match value {
            Predicate::<Ty>::Projection {
                base,
                label,
                returns,
            } => Self::Projection {
                base,
                label,
                returns,
            },
            Predicate::<Ty>::Conforms {
                param,
                protocol_id,
                span,
            } => Self::Conforms {
                param,
                protocol_id,
                span,
            },
            Predicate::<Ty>::Equals { lhs, rhs } => Self::Equals {
                lhs: lhs.into(),
                rhs: rhs.into(),
            },
            Predicate::<Ty>::HasField { row, label, ty } => Self::HasField {
                row,
                label,
                ty: ty.into(),
            },
            Predicate::<Ty>::Member {
                receiver,
                label,
                ty,
            } => Self::Member {
                receiver: receiver.into(),
                label,
                ty: ty.into(),
            },
            Predicate::<Ty>::TypeMember {
                base: owner,
                member,
                returns,
                generics,
            } => Self::TypeMember {
                base: owner.into(),
                member: member.clone(),
                returns: returns.into(),
                generics: generics.into_iter().map(|g| g.into()).collect(),
            },
            Predicate::<Ty>::Call {
                callee,
                args,
                returns,
                receiver,
            } => Self::Call {
                callee: callee.into(),
                args: args.into_iter().map(|arg| arg.into()).collect(),
                returns: returns.into(),
                receiver: receiver.map(|r| r.into()),
            },
        }
    }
}

impl Predicate<InferTy> {
    pub fn apply(&self, substitutions: &mut UnificationSubstitutions) -> Self {
        match self {
            Self::Projection {
                base,
                label,
                returns,
            } => Self::Projection {
                base: apply(base.clone(), substitutions),
                returns: apply(returns.clone(), substitutions),
                label: label.clone(),
            },
            Self::Conforms {
                param,
                protocol_id,
                span,
            } => Self::Conforms {
                param: *param,
                protocol_id: *protocol_id,
                span: *span,
            },
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
            Self::Equals { lhs, rhs } => Self::Equals {
                lhs: apply(lhs.clone(), substitutions),
                rhs: apply(rhs.clone(), substitutions),
            },
        }
    }

    pub fn instantiate(
        &self,
        id: NodeID,
        substitutions: &InstantiationSubstitutions,
        span: Span,
        level: Level,
    ) -> Constraint {
        match self.clone() {
            Self::Projection {
                base,
                label,
                returns,
            } => Constraint::Projection(Projection {
                node_id: id,
                base: instantiate_ty(id, base, substitutions, level),
                label,
                result: instantiate_ty(id, returns, substitutions, level),
                cause: ConstraintCause::Internal,
                span,
            }),
            Self::Conforms {
                param,
                protocol_id,
                span,
            } => Constraint::Conforms(Conforms {
                ty: instantiate_ty(id, InferTy::Param(param), substitutions, level),
                protocol_id,
                span,
            }),
            Self::Equals { lhs, rhs } => Constraint::Equals(Equals {
                lhs: instantiate_ty(id, lhs, substitutions, level),
                rhs: instantiate_ty(id, rhs, substitutions, level),
                cause: ConstraintCause::Internal,
                span,
            }),
            Self::HasField { row, label, ty } => Constraint::HasField(HasField {
                row: instantiate_row(id, InferRow::Param(row), substitutions, level),
                label,
                ty: instantiate_ty(id, ty, substitutions, level),
                cause: ConstraintCause::Internal,
                span,
            }),
            Self::Member {
                receiver,
                label,
                ty,
            } => Constraint::Member(Member {
                node_id: id,
                receiver: instantiate_ty(id, receiver, substitutions, level),
                label,
                ty: instantiate_ty(id, ty, substitutions, level),
                cause: ConstraintCause::Internal,
                span,
            }),
            Self::TypeMember {
                base,
                member,
                returns,
                generics,
            } => Constraint::TypeMember(TypeMember {
                base: instantiate_ty(id, base, substitutions, level),
                node_id: id,
                name: member,
                generics: generics
                    .iter()
                    .map(|g| instantiate_ty(id, g.clone(), substitutions, level))
                    .collect(),
                result: instantiate_ty(id, returns, substitutions, level),
                cause: ConstraintCause::Internal,
                span,
            }),
            Self::Call {
                callee,
                args,
                returns,
                receiver,
            } => Constraint::Call(Call {
                callee_id: id,
                callee: instantiate_ty(id, callee, substitutions, level),
                args: args
                    .iter()
                    .map(|f| instantiate_ty(id, f.clone(), substitutions, level))
                    .collect(),
                type_args: vec![],
                returns: instantiate_ty(id, returns, substitutions, level),
                receiver: receiver.map(|r| instantiate_ty(id, r.clone(), substitutions, level)),
                span,
                cause: ConstraintCause::Internal,
                level,
            }),
        }
    }
}

impl<T: SomeType> std::fmt::Debug for Predicate<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::Projection {
                base,
                label,
                returns,
            } => {
                write!(f, "*projection({base:?}.{label:?})->{returns:?}")
            }
            Predicate::Conforms {
                param, protocol_id, ..
            } => {
                write!(f, "*conforms({param:?}, {protocol_id:?})")
            }
            Predicate::HasField { row, label, ty } => {
                write!(f, "*hasfield({label}: {ty:?}, {row:?})")
            }
            Predicate::Equals { lhs, rhs } => {
                write!(f, "*eq({lhs:?} = {rhs:?})")
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
        }
    }
}
