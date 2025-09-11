use crate::{
    label::Label,
    node_id::NodeID,
    span::Span,
    types::{
        row::Row,
        scheme::Predicate,
        ty::Ty,
        type_operations::{UnificationSubstitutions, apply, apply_row},
    },
};

#[derive(Debug)]
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
    Internal,
}

#[derive(Debug)]
pub struct Equals {
    pub lhs: Ty,
    pub rhs: Ty,
    pub cause: ConstraintCause,
}

#[derive(Debug)]
pub struct HasField {
    pub row: Row,
    pub label: Label,
    pub ty: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

#[derive(Debug)]
pub enum Constraint {
    Equals(Equals),
    HasField(HasField),
}

impl Constraint {
    pub fn apply(mut self, subs: &mut UnificationSubstitutions) -> Constraint {
        match &mut self {
            Constraint::Equals(e) => {
                e.lhs = apply(e.lhs.clone(), subs);
                e.rhs = apply(e.rhs.clone(), subs);
            }
            Constraint::HasField(h) => {
                h.row = apply_row(h.row.clone(), subs);
                h.ty = apply(h.ty.clone(), subs);
            }
        }
        self
    }

    pub fn into_predicate(&self, substitutions: &mut UnificationSubstitutions) -> Predicate {
        match self {
            Self::HasField(has_field) => {
                let Row::Param(row_param) = apply_row(has_field.row.clone(), substitutions) else {
                    panic!("invariant violated: HasField predicate must be for ")
                };
                Predicate::HasField {
                    row: row_param,
                    label: has_field.label.clone(),
                    ty: apply(has_field.ty.clone(), substitutions),
                }
            }
            _ => unimplemented!("No predicate for constraint: {self:?}"),
        }
    }
}
