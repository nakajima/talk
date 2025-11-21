use crate::{
    node_id::NodeID,
    span::Span,
    types::{
        constraints::{
            call::Call, conforms::Conforms, equals::Equals, has_field::HasField, member::Member,
            projection::Projection, type_member::TypeMember,
        },
        infer_row::InferRow,
        infer_ty::InferTy,
        predicate::Predicate,
        type_operations::{
            UnificationSubstitutions, apply, apply_mult, apply_row, substitute, substitute_mult,
            substitute_row,
        },
    },
};
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
    pub fn is_generalizable(&self) -> bool {
        match self {
            Constraint::Call(..) => true,
            Constraint::Equals(..) => true,
            Constraint::HasField(..) => true,
            Constraint::Member(..) => true,
            Constraint::Conforms(..) => false,
            Constraint::TypeMember(..) => true,
            Constraint::Projection(..) => true,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            Constraint::Call(c) => c.span,
            Constraint::Equals(c) => c.span,
            Constraint::HasField(c) => c.span,
            Constraint::Member(c) => c.span,
            Constraint::Conforms(c) => c.span,
            Constraint::TypeMember(c) => c.span,
            Constraint::Projection(c) => c.span,
        }
    }

    pub fn apply(mut self, substitutions: &mut UnificationSubstitutions) -> Constraint {
        match &mut self {
            Constraint::Call(call) => {
                call.receiver = call.receiver.clone().map(|r| apply(r, substitutions));
                call.callee = apply(call.callee.clone(), substitutions);
                call.args = call
                    .args
                    .iter()
                    .map(|f| apply(f.clone(), substitutions))
                    .collect();
                call.returns = apply(call.returns.clone(), substitutions);
            }
            Constraint::Projection(c) => {
                c.base = apply(c.base.clone(), substitutions);
                c.result = apply(c.result.clone(), substitutions);
            }
            Constraint::Conforms(c) => {
                c.ty = apply(c.ty.clone(), substitutions);
            }
            Constraint::Equals(e) => {
                e.lhs = apply(e.lhs.clone(), substitutions);
                e.rhs = apply(e.rhs.clone(), substitutions);
            }
            Constraint::HasField(h) => {
                h.row = apply_row(h.row.clone(), substitutions);
                h.ty = apply(h.ty.clone(), substitutions);
            }
            Constraint::Member(member) => {
                member.ty = apply(member.ty.clone(), substitutions);
                member.receiver = apply(member.receiver.clone(), substitutions)
            }
            Constraint::TypeMember(c) => {
                c.base = apply(c.base.clone(), substitutions);
                c.result = apply(c.result.clone(), substitutions);
                c.generics = apply_mult(c.generics.clone(), substitutions);
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

    #[instrument(skip(substitutions), ret)]
    pub fn into_predicate(
        &self,
        substitutions: &mut UnificationSubstitutions,
    ) -> Option<Predicate<InferTy>> {
        tracing::debug!(
            "converting {:?} to predicate",
            self.clone().apply(substitutions)
        );
        let pred = match self {
            Self::HasField(has_field) => {
                let InferRow::Param(row_param) = apply_row(has_field.row.clone(), substitutions)
                else {
                    panic!(
                        "HasField predicate must be for row, got: {:?}",
                        apply_row(has_field.row.clone(), substitutions)
                    )
                };
                Predicate::HasField {
                    row: row_param,
                    label: has_field.label.clone(),
                    ty: apply(has_field.ty.clone(), substitutions),
                }
            }
            Self::Member(member) => Predicate::Member {
                receiver: apply(member.receiver.clone(), substitutions),
                label: member.label.clone(),
                ty: apply(member.ty.clone(), substitutions),
                node_id: member.node_id,
            },
            Self::Call(call) => Predicate::Call {
                callee: apply(call.callee.clone(), substitutions),
                args: call
                    .args
                    .iter()
                    .map(|f| apply(f.clone(), substitutions))
                    .collect(),
                returns: apply(call.returns.clone(), substitutions),
                receiver: call
                    .receiver
                    .as_ref()
                    .map(|r| apply(r.clone(), substitutions)),
            },
            Self::Equals(equals) => Predicate::Equals {
                lhs: apply(equals.lhs.clone(), substitutions),
                rhs: apply(equals.rhs.clone(), substitutions),
            },
            Self::Conforms(conforms) => {
                let InferTy::Param(param) = conforms.ty else {
                    panic!("didn't get param for conforms predicate: {:?}", conforms.ty);
                };

                Predicate::Conforms {
                    param,
                    protocol_id: conforms.protocol_id,
                    span: conforms.span,
                }
            }
            Self::Projection(projection) => Predicate::Projection {
                protocol_id: projection.protocol_id,
                base: apply(projection.base.clone(), substitutions),
                label: projection.label.clone(),
                returns: apply(projection.result.clone(), substitutions),
            },
            _ => return None,
        };

        Some(pred)
    }
}
