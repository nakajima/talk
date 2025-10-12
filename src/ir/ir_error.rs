use std::error::Error;

use crate::node_id::NodeID;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IRError {
    CouldNotParse(String),
    InvalidValueConversion(String),
    InvalidAssignmentTarget(String),
    InvalidFieldAccess(String),
    TypeNotFound(NodeID),
}

impl Error for IRError {}

impl std::fmt::Display for IRError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
