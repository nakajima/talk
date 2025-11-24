use crate::{
    label::Label,
    name_resolution::symbol::ProtocolId,
    node_id::NodeID,
    types::{
        constraints::{
            call::Call, conforms::Conforms, constraint::Constraint, equals::Equals,
            has_field::HasField, member::Member, projection::Projection, store::ConstraintStore,
            type_member::TypeMember,
        },
        infer_row::{InferRow, RowParamId},
        infer_ty::{InferTy, Level, TypeParamId},
        solve_context::Solve,
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
        protocol_id: Option<ProtocolId>,
    },
    Conforms {
        param: TypeParamId,
        protocol_id: ProtocolId,
    },
    Member {
        receiver: T,
        label: Label,
        ty: T,
        node_id: NodeID,
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
                protocol_id,
                base,
                label,
                returns,
            } => Self::Projection {
                base,
                label,
                returns,
                protocol_id,
            },
            Predicate::<InferTy>::Conforms { param, protocol_id } => {
                Self::Conforms { param, protocol_id }
            }
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
                node_id,
            } => Self::Member {
                receiver: receiver.into(),
                label,
                ty: ty.into(),
                node_id,
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
                protocol_id,
                base,
                label,
                returns,
            } => Self::Projection {
                protocol_id,
                base,
                label,
                returns,
            },
            Predicate::<Ty>::Conforms { param, protocol_id } => {
                Self::Conforms { param, protocol_id }
            }
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
                node_id,
            } => Self::Member {
                receiver: receiver.into(),
                label,
                ty: ty.into(),
                node_id,
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
                protocol_id,
                base,
                label,
                returns,
            } => Self::Projection {
                protocol_id: *protocol_id,
                base: apply(base.clone(), substitutions),
                returns: apply(returns.clone(), substitutions),
                label: label.clone(),
            },
            Self::Conforms { param, protocol_id } => Self::Conforms {
                param: *param,
                protocol_id: *protocol_id,
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
                node_id,
            } => Self::Member {
                receiver: apply(receiver.clone(), substitutions),
                label: label.clone(),
                ty: apply(ty.clone(), substitutions),
                node_id: *node_id,
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

    pub fn instantiate<'a>(
        &self,
        id: NodeID,
        constraints: &'a mut ConstraintStore,
        context: &mut impl Solve,
    ) -> &'a Constraint {
        let level = context.level();
        match self.clone() {
            Self::Projection {
                base,
                label,
                returns,
                protocol_id,
            } => constraints.wants_projection(
                id,
                instantiate_ty(id, base, context.instantiations_mut(), level),
                label,
                protocol_id,
                instantiate_ty(id, returns, context.instantiations_mut(), level),
                &context.group_info(),
            ),
            Self::Conforms { param, protocol_id } => constraints.wants_conforms(
                instantiate_ty(
                    id,
                    InferTy::Param(param),
                    context.instantiations_mut(),
                    level,
                ),
                protocol_id,
            ),
            Self::Equals { lhs, rhs } => constraints.wants_equals(
                instantiate_ty(id, lhs, context.instantiations_mut(), level),
                instantiate_ty(id, rhs, context.instantiations_mut(), level),
            ),
            Self::HasField { row, label, ty } => constraints._has_field(
                instantiate_row(
                    id,
                    InferRow::Param(row),
                    context.instantiations_mut(),
                    level,
                ),
                label,
                instantiate_ty(id, ty, context.instantiations_mut(), level),
                &context.group_info(),
            ),
            Self::Member {
                receiver,
                label,
                ty,
                node_id,
            } => constraints.wants_member(
                node_id,
                instantiate_ty(id, receiver, context.instantiations_mut(), level),
                label,
                instantiate_ty(id, ty, context.instantiations_mut(), level),
                &context.group_info(),
            ),
            Self::TypeMember {
                base,
                member,
                returns,
                generics,
            } => constraints.wants_type_member(
                instantiate_ty(id, base, context.instantiations_mut(), level),
                member,
                generics
                    .iter()
                    .map(|g| instantiate_ty(id, g.clone(), context.instantiations_mut(), level))
                    .collect(),
                instantiate_ty(id, returns, context.instantiations_mut(), level),
                id,
                &context.group_info(),
            ),
            Self::Call {
                callee,
                args,
                returns,
                receiver,
            } => constraints.wants_call(
                id,
                instantiate_ty(id, callee, context.instantiations_mut(), level),
                args.iter()
                    .map(|f| instantiate_ty(id, f.clone(), context.instantiations_mut(), level))
                    .collect(),
                Default::default(),
                instantiate_ty(id, returns, context.instantiations_mut(), level),
                receiver.map(|r| instantiate_ty(id, r, context.instantiations_mut(), level)),
                &context.group_info(),
            ),
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
                protocol_id,
            } => {
                write!(
                    f,
                    "*projection({base:?}.{label:?}, {protocol_id:?})->{returns:?}"
                )
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
                node_id,
                receiver,
                label,
                ty,
            } => {
                write!(f, "*member({receiver:?}.{label} = {ty:?})[{node_id:?}]")
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
