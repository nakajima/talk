use crate::{
    compiling::module::ModuleId,
    label::Label,
    name_resolution::symbol::ProtocolId,
    node_id::NodeID,
    types::{
        constraints::{
            constraint::{Constraint, ConstraintCause},
            store::ConstraintStore,
        },
        infer_row::{InferRow, RowParamId},
        infer_ty::{InferTy, TypeParamId},
        mappable::Mappable,
        solve_context::SolveContext,
        ty::{SomeType, Ty},
        type_operations::{UnificationSubstitutions, curry, instantiate_row, instantiate_ty},
        type_session::TypeSession,
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
        base: T,
        label: Label,
        returns: T,
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
            } => Predicate::Projection {
                base: base.into(),
                label,
                returns: returns.into(),
                protocol_id,
            },
            Predicate::<InferTy>::Conforms { param, protocol_id } => {
                Predicate::Conforms { param, protocol_id }
            }
            Predicate::<InferTy>::Equals { lhs, rhs } => Predicate::Equals {
                lhs: lhs.into(),
                rhs: rhs.into(),
            },
            Predicate::<InferTy>::HasField { row, label, ty } => Predicate::HasField {
                row,
                label,
                ty: ty.into(),
            },
            Predicate::<InferTy>::Member {
                receiver,
                label,
                ty,
                node_id,
            } => Predicate::Member {
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
            } => Predicate::TypeMember {
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
            } => Predicate::Call {
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
        value.mapping(&mut |t| t.into(), &mut |r| r.into())
    }
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for Predicate<T> {
    type Output = Predicate<U>;
    fn mapping(
        self,
        ty_map: &mut impl FnMut(T) -> U,
        _row_map: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        match self {
            Predicate::Projection {
                protocol_id,
                base,
                label,
                returns,
            } => Predicate::Projection {
                protocol_id,
                base: ty_map(base),
                returns: ty_map(returns),
                label,
            },
            Predicate::Conforms { param, protocol_id } => {
                Predicate::Conforms { param, protocol_id }
            }
            Predicate::HasField { row, label, ty } => Predicate::HasField {
                row,
                label,
                ty: ty_map(ty),
            },
            Predicate::Member {
                receiver,
                label,
                ty,
                node_id,
            } => Predicate::Member {
                receiver: ty_map(receiver),
                label,
                ty: ty_map(ty),
                node_id,
            },
            Predicate::TypeMember {
                base: owner,
                member,
                returns,
                generics,
            } => Predicate::TypeMember {
                base: ty_map(owner),
                member,
                returns: ty_map(returns),
                generics: generics.into_iter().map(ty_map).collect(),
            },
            Predicate::Call {
                callee,
                args,
                returns,
                receiver,
            } => Predicate::Call {
                callee: ty_map(callee),
                args: args.into_iter().map(&mut *ty_map).collect(),
                returns: ty_map(returns),
                receiver: receiver.map(ty_map),
            },
            Predicate::Equals { lhs, rhs } => Predicate::Equals {
                lhs: ty_map(lhs),
                rhs: ty_map(rhs),
            },
        }
    }
}

impl<T: SomeType> Predicate<T> {
    pub fn import(self, module_id: ModuleId) -> Self {
        self.mapping(&mut |t| t.clone().import(module_id), &mut |r| r)
    }
}

impl Predicate<InferTy> {
    pub fn apply(
        &self,
        substitutions: &mut UnificationSubstitutions,
        session: &mut TypeSession,
    ) -> Self {
        self.clone().mapping(
            &mut |t| session.apply(t.clone(), substitutions),
            &mut |r| r, /* session.apply already handles rows */
        )
    }

    pub fn instantiate<'a>(
        &self,
        id: NodeID,
        constraints: &'a mut ConstraintStore,
        context: &mut SolveContext,
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
                id,
                instantiate_ty(
                    id,
                    InferTy::Param(param, vec![protocol_id]),
                    context.instantiations_mut(),
                    level,
                ),
                protocol_id,
                &context.group_info(),
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
                None,
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
                ConstraintCause::Internal,
            ),
            Self::Call {
                callee,
                args,
                returns,
                receiver,
            } => constraints.wants_call(
                id,
                id,
                instantiate_ty(id, callee, context.instantiations_mut(), level),
                args.iter()
                    .map(|f| instantiate_ty(id, f.clone(), context.instantiations_mut(), level))
                    .collect(),
                Default::default(),
                instantiate_ty(id, returns.clone(), context.instantiations_mut(), level),
                curry(args, returns, InferRow::Var(0.into()).into()),
                receiver.map(|r| instantiate_ty(id, r, context.instantiations_mut(), level)),
                &context.group_info(),
                InferRow::Var(0.into()),
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
