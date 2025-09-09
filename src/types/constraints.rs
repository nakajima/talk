use crate::{
    label::Label,
    node_id::NodeID,
    span::Span,
    types::{row::Row, ty::Ty},
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
