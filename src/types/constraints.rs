use crate::{node_id::NodeID, types::ty::Ty};

#[derive(Debug)]
pub enum ConstraintCause {
    Annotation(NodeID),
    Literal(NodeID),
    Assignment(NodeID),
    Call(NodeID),
    Condition(NodeID),
    Pattern(NodeID),
    Internal,
}

#[derive(Debug)]
pub struct Equals {
    pub lhs: Ty,
    pub rhs: Ty,
    pub cause: ConstraintCause,
}

#[derive(Debug)]
pub enum Constraint {
    Equals(Equals),
}
