use crate::{
    node_id::NodeID,
    types::{
        constraints::{
            call::Call, conforms::Conforms, equals::Equals, has_field::HasField, member::Member,
            projection::Projection, store::ConstraintId, type_member::TypeMember,
        },
        infer_row::InferRow,
        infer_ty::InferTy,
        predicate::Predicate,
        type_operations::{UnificationSubstitutions, substitute, substitute_mult, substitute_row},
        type_session::TypeSession,
    },
};
use indexmap::IndexSet;
use rustc_hash::FxHashMap;
use tracing::instrument;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constraint {
    Call(Call),
    Equals(Equals),
    HasField(HasField),
    Member(Member),
    Conforms(Conforms),
    TypeMember(TypeMember),
    Projection(Projection),
}

impl Constraint {
    pub fn id(&self) -> ConstraintId {
        match self {
            Constraint::Call(c) => c.id,
            Constraint::Equals(c) => c.id,
            Constraint::HasField(c) => c.id,
            Constraint::Member(c) => c.id,
            Constraint::Conforms(c) => c.id,
            Constraint::TypeMember(c) => c.id,
            Constraint::Projection(c) => c.id,
        }
    }

    pub fn is_generalizable(&self) -> bool {
        match self {
            Constraint::Call(..) => false,
            Constraint::Equals(..) => true,
            Constraint::HasField(..) => true,
            Constraint::Member(..) => false,
            Constraint::Conforms(..) => true,
            Constraint::TypeMember(..) => true,
            Constraint::Projection(..) => true,
        }
    }

    pub fn apply(
        mut self,
        substitutions: &mut UnificationSubstitutions,
        session: &mut TypeSession,
    ) -> Constraint {
        match &mut self {
            Constraint::Call(call) => {
                call.receiver = call
                    .receiver
                    .clone()
                    .map(|r| session.apply(r, substitutions));
                call.callee = session.apply(call.callee.clone(), substitutions);
                call.args = call
                    .args
                    .iter()
                    .map(|f| session.apply(f.clone(), substitutions))
                    .collect();
                call.returns = session.apply(call.returns.clone(), substitutions);
            }
            Constraint::Projection(c) => {
                c.base = session.apply(c.base.clone(), substitutions);
                c.result = session.apply(c.result.clone(), substitutions);
            }
            Constraint::Conforms(c) => {
                c.ty = session.apply(c.ty.clone(), substitutions);
            }
            Constraint::Equals(e) => {
                e.lhs = session.apply(e.lhs.clone(), substitutions);
                e.rhs = session.apply(e.rhs.clone(), substitutions);
            }
            Constraint::HasField(h) => {
                h.row = session.apply_row(h.row.clone(), substitutions);
                h.ty = session.apply(h.ty.clone(), substitutions);
            }
            Constraint::Member(member) => {
                member.ty = session.apply(member.ty.clone(), substitutions);
                member.receiver = session.apply(member.receiver.clone(), substitutions)
            }
            Constraint::TypeMember(c) => {
                c.base = session.apply(c.base.clone(), substitutions);
                c.result = session.apply(c.result.clone(), substitutions);
                c.generics = session.apply_mult(c.generics.clone(), substitutions);
            }
        }
        self
    }

    pub fn substitute(&self, substitutions: &FxHashMap<InferTy, InferTy>) -> Constraint {
        let mut copy = self.clone();

        match &mut copy {
            Constraint::Call(call) => {
                call.receiver = call.receiver.clone().map(|r| substitute(r, substitutions));
                call.callee = substitute(call.callee.clone(), substitutions);
                call.args = call
                    .args
                    .iter()
                    .map(|f| substitute(f.clone(), substitutions))
                    .collect();
                call.returns = substitute(call.returns.clone(), substitutions);
            }
            Constraint::Projection(c) => {
                c.base = substitute(c.base.clone(), substitutions);
                c.result = substitute(c.result.clone(), substitutions);
            }
            Constraint::Conforms(..) => (),
            Constraint::Equals(e) => {
                e.lhs = substitute(e.lhs.clone(), substitutions);
                e.rhs = substitute(e.rhs.clone(), substitutions);
            }
            Constraint::HasField(h) => {
                h.row = substitute_row(h.row.clone(), substitutions);
                h.ty = substitute(h.ty.clone(), substitutions);
            }
            Constraint::Member(member) => {
                member.ty = substitute(member.ty.clone(), substitutions);
                member.receiver = substitute(member.receiver.clone(), substitutions)
            }
            Constraint::TypeMember(c) => {
                c.base = substitute(c.base.clone(), substitutions);
                c.result = substitute(c.result.clone(), substitutions);
                c.generics = substitute_mult(&c.generics, substitutions);
            }
        }

        copy
    }

    #[instrument(skip(substitutions, session), ret)]
    pub fn into_predicate(
        &self,
        substitutions: &mut UnificationSubstitutions,
        session: &mut TypeSession,
    ) -> Option<Predicate<InferTy>> {
        let pred = match self {
            #[allow(clippy::panic)]
            Self::HasField(has_field) => {
                let InferRow::Param(row_param) =
                    session.apply_row(has_field.row.clone(), substitutions)
                else {
                    panic!(
                        "HasField predicate must be for row, got: {:?}",
                        session.apply_row(has_field.row.clone(), substitutions)
                    )
                };
                Predicate::HasField {
                    row: row_param,
                    label: has_field.label.clone(),
                    ty: session.apply(has_field.ty.clone(), substitutions),
                }
            }
            Self::Member(member) => Predicate::Member {
                receiver: session.apply(member.receiver.clone(), substitutions),
                label: member.label.clone(),
                ty: session.apply(member.ty.clone(), substitutions),
                node_id: member.node_id,
            },
            Self::Call(call) => Predicate::Call {
                callee: session.apply(call.callee.clone(), substitutions),
                args: call
                    .args
                    .iter()
                    .map(|f| session.apply(f.clone(), substitutions))
                    .collect(),
                returns: session.apply(call.returns.clone(), substitutions),
                receiver: call
                    .receiver
                    .as_ref()
                    .map(|r| session.apply(r.clone(), substitutions)),
            },
            Self::Equals(equals) => Predicate::Equals {
                lhs: session.apply(equals.lhs.clone(), substitutions),
                rhs: session.apply(equals.rhs.clone(), substitutions),
            },
            Self::Conforms(conforms) => {
                let InferTy::Param(param) = session.apply(conforms.ty.clone(), substitutions)
                else {
                    unreachable!("didn't get param for conforms predicate: {:?}", conforms.ty);
                };

                Predicate::Conforms {
                    param,
                    protocol_id: conforms.protocol_id,
                }
            }
            Self::Projection(projection) => Predicate::Projection {
                protocol_id: projection.protocol_id,
                base: session.apply(projection.base.clone(), substitutions),
                label: projection.label.clone(),
                returns: session.apply(projection.result.clone(), substitutions),
            },
            _ => return None,
        };

        Some(pred)
    }

    pub fn collect_metas(&self) -> IndexSet<InferTy> {
        let mut out = IndexSet::default();
        match self {
            Constraint::Projection(c) => {
                out.extend(c.base.collect_metas());
                out.extend(c.result.collect_metas());
            }
            Constraint::Equals(equals) => {
                out.extend(equals.lhs.collect_metas());
                out.extend(equals.rhs.collect_metas());
            }
            Constraint::Member(member) => {
                out.extend(member.receiver.collect_metas());
                out.extend(member.ty.collect_metas());
            }
            Constraint::Call(call) => {
                out.extend(call.callee.collect_metas());
                for argument in &call.args {
                    out.extend(argument.collect_metas());
                }
                if let Some(receiver) = &call.receiver {
                    out.extend(receiver.collect_metas());
                }
                out.extend(call.returns.collect_metas());
            }
            Constraint::HasField(has_field) => {
                // The row meta is handled in your existing HasField block later.
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
        }

        out
    }
}
