use crate::{
    node_id::NodeID,
    span::Span,
    types::{
        constraints::{
            call::Call, construction::Construction, equals::Equals, has_field::HasField,
            member::Member,
        },
        row::Row,
        scheme::Predicate,
        type_operations::{UnificationSubstitutions, apply, apply_mult, apply_row},
    },
};

#[derive(Debug, Clone, Copy)]
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
    Internal,
}

#[derive(Debug, Clone)]
pub enum Constraint {
    Call(Call),
    Equals(Equals),
    HasField(HasField),
    Member(Member),
    Construction(Construction),
}

impl Constraint {
    pub fn span(&self) -> Span {
        match self {
            Constraint::Call(c) => c.span,
            Constraint::Equals(c) => c.span,
            Constraint::HasField(c) => c.span,
            Constraint::Member(c) => c.span,
            Constraint::Construction(c) => c.span,
        }
    }

    pub fn apply(mut self, substitutions: &mut UnificationSubstitutions) -> Constraint {
        match &mut self {
            Constraint::Call(call) => {
                call.callee = apply(call.callee.clone(), substitutions);
                call.args = call
                    .args
                    .iter()
                    .map(|f| apply(f.clone(), substitutions))
                    .collect();
                call.returns = apply(call.returns.clone(), substitutions);
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
            Constraint::Construction(construction) => {
                construction.callee = apply(construction.callee.clone(), substitutions);
                construction.args = apply_mult(construction.args.clone(), substitutions);
                construction.returns = apply(construction.returns.clone(), substitutions);
            }
        }
        self
    }

    pub fn into_predicate(&self, substitutions: &mut UnificationSubstitutions) -> Predicate {
        match self {
            Self::HasField(has_field) => {
                let Row::Param(row_param) = apply_row(has_field.row.clone(), substitutions) else {
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
            _ => unimplemented!("No predicate for constraint: {self:?}"),
        }
    }
}
