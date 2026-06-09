use crate::{
    compiling::module::ModuleId,
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    types::{
        constraints::{
            constraint::{Constraint, ConstraintCause},
            store::ConstraintStore,
        },
        infer_row::{Row, RowParamId},
        infer_ty::Ty,
        solve_context::SolveContext,
        type_args::TypeArgs,
        type_operations::{UnificationSubstitutions, curry},
        type_session::TypeSession,
    },
};

// Predicates are kinda like Constraint templates. They ride around with schemes and get instantiated
// into constraints when the scheme itself is instantiated.
#[derive(Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Predicate {
    HasField {
        row: RowParamId,
        label: Label,
        ty: Ty,
    },
    Projection {
        base: Ty,
        label: Label,
        returns: Ty,
        protocol_id: Option<ProtocolId>,
    },
    Conforms {
        param: Symbol,
        protocol_id: ProtocolId,
    },
    Member {
        receiver: Ty,
        label: Label,
        ty: Ty,
        node_id: NodeID,
    },
    Equals {
        lhs: Ty,
        rhs: Ty,
    },
    Call {
        callee: Ty,
        args: Vec<Ty>,
        returns: Ty,
    },
    TypeMember {
        base: Ty,
        member: Label,
        returns: Ty,
        generics: Vec<Ty>,
    },
}

impl Predicate {
    pub fn mapping(
        self,
        ty_map: &mut impl FnMut(Ty) -> Ty,
        _row_map: &mut impl FnMut(Row) -> Row,
    ) -> Self {
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
            } => Predicate::Call {
                callee: ty_map(callee),
                args: args.into_iter().map(&mut *ty_map).collect(),
                returns: ty_map(returns),
            },
            Predicate::Equals { lhs, rhs } => Predicate::Equals {
                lhs: ty_map(lhs),
                rhs: ty_map(rhs),
            },
        }
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        self.mapping(&mut |t| t.clone().import(module_id), &mut |r| r)
    }

    pub fn apply(
        &self,
        substitutions: &mut UnificationSubstitutions,
        session: &mut TypeSession,
    ) -> Self {
        self.clone().mapping(
            &mut |t| session.apply(&t, substitutions),
            &mut |r| r, /* session.apply already handles rows */
        )
    }

    pub fn instantiate<'a>(
        &self,
        id: NodeID,
        type_args: &TypeArgs,
        constraints: &'a mut ConstraintStore,
        context: &mut SolveContext,
    ) -> &'a Constraint {
        match self.clone() {
            Self::Projection {
                base,
                label,
                returns,
                protocol_id,
            } => constraints.wants_projection(
                id,
                type_args.apply(base),
                label,
                protocol_id,
                type_args.apply(returns),
                &context.group_info(),
            ),
            Self::Conforms { param, protocol_id } => constraints.wants_conforms(
                id,
                type_args.apply(Ty::Param(param, vec![protocol_id])),
                protocol_id,
                &context.group_info(),
            ),
            Self::Equals { lhs, rhs } => {
                constraints.wants_equals(type_args.apply(lhs), type_args.apply(rhs))
            }
            Self::HasField { row, label, ty } => constraints._has_field(
                type_args.apply_row(Row::Param(row)),
                label,
                type_args.apply(ty),
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
                type_args.apply(receiver),
                label,
                type_args.apply(ty),
                &context.group_info(),
            ),
            Self::TypeMember {
                base,
                member,
                returns,
                generics,
            } => constraints.wants_type_member(
                type_args.apply(base),
                member,
                generics.into_iter().map(|g| type_args.apply(g)).collect(),
                type_args.apply(returns),
                id,
                &context.group_info(),
                ConstraintCause::Internal,
            ),
            Self::Call {
                callee,
                args,
                returns,
            } => {
                let callee = type_args.apply(callee);
                let args = args
                    .into_iter()
                    .map(|arg| type_args.apply(arg))
                    .collect::<Vec<_>>();
                let returns = type_args.apply(returns);
                let callee_type = curry(args.clone(), returns.clone(), Row::Var(0.into()).into());
                constraints.wants_call(
                    id,
                    id,
                    callee,
                    args,
                    Default::default(),
                    returns,
                    callee_type,
                    &context.group_info(),
                    Row::Var(0.into()),
                )
            }
        }
    }
}

impl std::fmt::Debug for Predicate {
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
            } => write!(f, "*call({callee:?}({args:?}) = {returns:?})"),
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
