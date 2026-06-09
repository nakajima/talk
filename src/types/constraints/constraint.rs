use crate::{
    node_id::NodeID,
    types::{
        constraints::{
            call::Call,
            conforms::Conforms,
            default_ty::DefaultTy,
            equals::Equals,
            has_field::HasField,
            member::{Member, MemberCall},
            projection::Projection,
            row_subset::RowSubset,
            store::ConstraintId,
            type_member::TypeMember,
        },
        infer_row::Row,
        infer_ty::Ty,
        predicate::Predicate,
        type_operations::{UnificationSubstitutions, substitute, substitute_mult, substitute_row},
        type_session::TypeSession,
    },
};
use indexmap::IndexSet;
use rustc_hash::FxHashMap;
use tracing::instrument;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ConstraintCause {
    Annotation(NodeID),
    Member(NodeID),
    Literal(NodeID),
    Assignment(NodeID),
    Call(NodeID),
    Condition(NodeID),
    Pattern(NodeID),
    MatchArm(NodeID),
    CallTypeArg(NodeID),
    Conformance { node: NodeID, requirement: NodeID },
    TypeMember(NodeID),
    Internal,
}

impl ConstraintCause {
    pub fn label(&self) -> &'static str {
        match self {
            Self::Annotation(..) => "type annotation",
            Self::Member(..) => "member access",
            Self::Literal(..) => "literal",
            Self::Assignment(..) => "assignment",
            Self::Call(..) => "call",
            Self::Condition(..) => "condition",
            Self::Pattern(..) => "pattern",
            Self::MatchArm(..) => "match arm",
            Self::CallTypeArg(..) => "call type argument",
            Self::Conformance { .. } => "conformance",
            Self::TypeMember(..) => "type member",
            Self::Internal => "internal",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(clippy::large_enum_variant)]
pub enum Constraint {
    Call(Call),
    Equals(Equals),
    HasField(HasField),
    Member(Member),
    MemberCall(MemberCall),
    Conforms(Conforms),
    TypeMember(TypeMember),
    Projection(Projection),
    RowSubset(RowSubset),
    DefaultTy(DefaultTy),
}

impl Constraint {
    pub fn id(&self) -> ConstraintId {
        match self {
            Constraint::Call(c) => c.id,
            Constraint::Equals(c) => c.id,
            Constraint::HasField(c) => c.id,
            Constraint::Member(c) => c.id,
            Constraint::MemberCall(c) => c.id,
            Constraint::Conforms(c) => c.id,
            Constraint::TypeMember(c) => c.id,
            Constraint::Projection(c) => c.id,
            Constraint::RowSubset(c) => c.id,
            Constraint::DefaultTy(c) => c.id,
        }
    }

    pub fn diagnostic_node_id(&self) -> Option<NodeID> {
        match self {
            Constraint::Call(call) => Some(call.call_node_id),
            Constraint::Equals(equals) => equals.node_id,
            Constraint::Member(member) => Some(member.node_id),
            Constraint::MemberCall(member_call) => Some(member_call.member_node_id),
            Constraint::Conforms(conforms) => Some(conforms.conformance_node_id),
            Constraint::TypeMember(type_member) => Some(type_member.node_id),
            Constraint::Projection(projection) => Some(projection.node_id),
            Constraint::HasField(has_field) => has_field.node_id,
            Constraint::RowSubset(c) => c.node_id,
            Constraint::DefaultTy(c) => Some(c.node_id),
        }
    }

    pub fn apply(
        mut self,
        substitutions: &mut UnificationSubstitutions,
        session: &mut TypeSession,
    ) -> Constraint {
        match &mut self {
            Constraint::Call(call) => {
                call.callee = session.apply(&call.callee, substitutions);
                call.args = call
                    .args
                    .iter()
                    .map(|f| session.apply(f, substitutions))
                    .collect();
                call.returns = session.apply(&call.returns, substitutions);
            }
            Constraint::Projection(c) => {
                c.base = session.apply(&c.base, substitutions);
                c.result = session.apply(&c.result, substitutions);
            }
            Constraint::Conforms(c) => {
                c.ty = session.apply(&c.ty, substitutions);
            }
            Constraint::Equals(e) => {
                e.lhs = session.apply(&e.lhs, substitutions);
                e.rhs = session.apply(&e.rhs, substitutions);
            }
            Constraint::DefaultTy(e) => {
                e.var = session.apply(&e.var, substitutions);
                e.ty = session.apply(&e.ty, substitutions);
                e.allowed = e
                    .allowed
                    .iter()
                    .map(|ty| session.apply(ty, substitutions))
                    .collect();
            }
            Constraint::HasField(h) => {
                h.row = session.apply_row(&h.row, substitutions);
                h.ty = session.apply(&h.ty, substitutions);
            }
            Constraint::Member(member) => {
                member.ty = session.apply(&member.ty, substitutions);
                member.receiver = session.apply(&member.receiver, substitutions)
            }
            Constraint::MemberCall(member_call) => {
                member_call.ty = session.apply(&member_call.ty, substitutions);
                member_call.receiver = session.apply(&member_call.receiver, substitutions);
                member_call.returns = session.apply(&member_call.returns, substitutions);
            }
            Constraint::TypeMember(c) => {
                c.base = session.apply(&c.base, substitutions);
                c.result = session.apply(&c.result, substitutions);
                c.generics = session.apply_mult(&c.generics, substitutions);
            }
            Constraint::RowSubset(c) => {
                c.left = session.apply_row(&c.left, substitutions);
                c.right = session.apply_row(&c.right, substitutions);
            }
        }
        self
    }

    pub fn substitute(&self, substitutions: &FxHashMap<Ty, Ty>) -> Constraint {
        let mut copy = self.clone();

        match &mut copy {
            Constraint::Call(call) => {
                call.callee = substitute(&call.callee, substitutions);
                call.args = call
                    .args
                    .iter()
                    .map(|f| substitute(f, substitutions))
                    .collect();
                call.returns = substitute(&call.returns, substitutions);
            }
            Constraint::Projection(c) => {
                c.base = substitute(&c.base, substitutions);
                c.result = substitute(&c.result, substitutions);
            }
            Constraint::DefaultTy(c) => {
                c.var = substitute(&c.var, substitutions);
                c.ty = substitute(&c.ty, substitutions);
                c.allowed = c
                    .allowed
                    .iter()
                    .map(|ty| substitute(ty, substitutions))
                    .collect();
            }
            Constraint::Conforms(..) => (),
            Constraint::Equals(e) => {
                e.lhs = substitute(&e.lhs, substitutions);
                e.rhs = substitute(&e.rhs, substitutions);
            }
            Constraint::HasField(h) => {
                h.row = substitute_row(&h.row, substitutions);
                h.ty = substitute(&h.ty, substitutions);
            }
            Constraint::Member(member) => {
                member.ty = substitute(&member.ty, substitutions);
                member.receiver = substitute(&member.receiver, substitutions)
            }
            Constraint::MemberCall(member_call) => {
                member_call.ty = substitute(&member_call.ty, substitutions);
                member_call.receiver = substitute(&member_call.receiver, substitutions);
                member_call.returns = substitute(&member_call.returns, substitutions);
            }
            Constraint::TypeMember(c) => {
                c.base = substitute(&c.base, substitutions);
                c.result = substitute(&c.result, substitutions);
                c.generics = substitute_mult(&c.generics, substitutions);
            }
            Constraint::RowSubset(c) => {
                c.left = substitute_row(&c.left, substitutions);
                c.right = substitute_row(&c.right, substitutions);
            }
        }

        copy
    }

    #[instrument(skip(substitutions, session), ret)]
    pub fn into_predicate(
        &self,
        substitutions: &mut UnificationSubstitutions,
        session: &mut TypeSession,
    ) -> Option<Predicate> {
        let pred = match self {
            #[allow(clippy::panic)]
            Self::HasField(has_field) => {
                let Row::Param(row_param) = session.apply_row(&has_field.row, substitutions) else {
                    panic!(
                        "HasField predicate must be for row, got: {:?}",
                        session.apply_row(&has_field.row, substitutions)
                    )
                };
                Predicate::HasField {
                    row: row_param,
                    label: has_field.label.clone(),
                    ty: session.apply(&has_field.ty, substitutions),
                }
            }
            Self::Member(member) => {
                let receiver = session.apply(&member.receiver, substitutions);
                let bounds = match &receiver {
                    Ty::Param(_, bounds) => bounds.clone(),
                    Ty::Var { id, .. } => match session.lookup_type_param_origin(*id) {
                        Some(Ty::Param(_, bounds)) => bounds,
                        _ => vec![],
                    },
                    _ => vec![],
                };

                let mut candidates = vec![];
                for protocol_id in bounds {
                    if let Some((requirement, _source)) =
                        session.lookup_member(&protocol_id.into(), &member.label)
                        && !candidates.contains(&requirement)
                    {
                        candidates.push(requirement);
                    }
                }
                if candidates.len() > 1 {
                    return None;
                }

                Predicate::Member {
                    receiver,
                    label: member.label.clone(),
                    ty: session.apply(&member.ty, substitutions),
                    node_id: member.node_id,
                }
            }
            Self::MemberCall(member_call) => {
                let receiver = session.apply(&member_call.receiver, substitutions);
                let bounds = match &receiver {
                    Ty::Param(_, bounds) => bounds.clone(),
                    Ty::Var { id, .. } => match session.lookup_type_param_origin(*id) {
                        Some(Ty::Param(_, bounds)) => bounds,
                        _ => vec![],
                    },
                    _ => vec![],
                };

                let mut candidates = vec![];
                for protocol_id in bounds {
                    if let Some((requirement, _source)) =
                        session.lookup_member(&protocol_id.into(), &member_call.label)
                        && !candidates.contains(&requirement)
                    {
                        candidates.push(requirement);
                    }
                }
                if candidates.len() > 1 {
                    return None;
                }

                Predicate::Member {
                    receiver,
                    label: member_call.label.clone(),
                    ty: session.apply(&member_call.ty, substitutions),
                    node_id: member_call.member_node_id,
                }
            }
            Self::Call(call) => Predicate::Call {
                callee: session.apply(&call.callee, substitutions),
                args: call
                    .args
                    .iter()
                    .map(|f| session.apply(f, substitutions))
                    .collect(),
                returns: session.apply(&call.returns, substitutions),
            },
            Self::Equals(equals) => Predicate::Equals {
                lhs: session.apply(&equals.lhs, substitutions),
                rhs: session.apply(&equals.rhs, substitutions),
            },
            Self::Conforms(conforms) => {
                let Ty::Param(param, _) = session.apply(&conforms.ty, substitutions) else {
                    // If the type resolved to a concrete type (not a type parameter),
                    // we can't generalize this constraint - it should have already been
                    // checked during constraint solving.
                    return None;
                };

                Predicate::Conforms {
                    param,
                    protocol_id: conforms.protocol_id,
                }
            }
            Self::Projection(projection) => {
                if !session.can_generalize_projection(
                    projection.protocol_id,
                    &projection.base,
                    &projection.label,
                    substitutions,
                ) {
                    return None;
                }

                Predicate::Projection {
                    protocol_id: projection.protocol_id,
                    base: session.apply(&projection.base, substitutions),
                    label: projection.label.clone(),
                    returns: session.apply(&projection.result, substitutions),
                }
            }
            _ => return None,
        };

        Some(pred)
    }

    pub fn collect_metas(&self) -> IndexSet<Ty> {
        let mut out = IndexSet::default();
        match self {
            Constraint::Projection(c) => {
                out.extend(c.base.collect_metas());
                out.extend(c.result.collect_metas());
            }
            Constraint::DefaultTy(c) => {
                out.extend(c.var.collect_metas());
                out.extend(c.ty.collect_metas());
                out.extend(c.allowed.iter().cloned().flat_map(|ty| ty.collect_metas()));
            }
            Constraint::Equals(equals) => {
                out.extend(equals.lhs.collect_metas());
                out.extend(equals.rhs.collect_metas());
            }
            Constraint::Member(member) => {
                out.extend(member.receiver.collect_metas());
                out.extend(member.ty.collect_metas());
            }
            Constraint::MemberCall(member_call) => {
                out.extend(member_call.receiver.collect_metas());
                out.extend(member_call.self_ty.collect_metas());
                out.extend(member_call.ty.collect_metas());
                out.extend(member_call.returns.collect_metas());
            }
            Constraint::Call(call) => {
                out.extend(call.callee.collect_metas());
                for argument in &call.args {
                    out.extend(argument.collect_metas());
                }
                out.extend(call.returns.collect_metas());
            }
            Constraint::HasField(has_field) => {
                out.extend(has_field.row.collect_metas());
                out.extend(has_field.ty.collect_metas());
            }
            Constraint::Conforms(c) => {
                out.extend(c.ty.collect_metas());
            }
            Constraint::TypeMember(c) => {
                out.extend(c.base.collect_metas());
                out.extend(c.result.collect_metas());
                for ty in &c.generics {
                    out.extend(ty.collect_metas());
                }
            }
            Constraint::RowSubset(c) => {
                out.extend(c.left.collect_metas());
                out.extend(c.right.collect_metas());
            }
        }

        out
    }
}
