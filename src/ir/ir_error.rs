use std::error::Error;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IRError {
    CouldNotParse(String),
    InvalidValueConversion(String),
    InvalidAssignmentTarget(String),
    InvalidFieldAccess(String),
    TypeNotFound(String),
}

impl Error for IRError {}

impl std::fmt::Display for IRError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
