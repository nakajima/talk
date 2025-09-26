use std::{error::Error, fmt::Display};

use crate::{name_resolution::symbol::TypeId, types::ty::Ty};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    TypeConstructorNotFound(TypeId),
    ExpectedRow(Ty),
    GenericArgCount {
        expected: u8,
        actual: u8,
    },
    InvalidUnification(Ty, Ty),
    OccursCheck(Ty),
    CalleeNotCallable(Ty),
    MemberNotFound(Ty, String),
    MissingConformanceRequirement(String),
    TypeNotFound(String),
    TypesDoesNotConform {
        type_id: TypeId,
        protocol_id: TypeId,
    },
}

impl Error for TypeError {}
impl Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeConstructorNotFound(id) => write!(f, "Type constructor not found: {id:?}"),
            Self::GenericArgCount { expected, actual } => {
                write!(f, "Expected {expected} type arguments, got {actual}")
            }
            Self::InvalidUnification(lhs, rhs) => {
                write!(f, "Invalid unification: {lhs:?} <> {rhs:?}")
            }
            Self::OccursCheck(ty) => {
                write!(f, "Recursive type not supported..... yet? {ty:?}")
            }
            Self::ExpectedRow(ty) => {
                write!(f, "Expected row, got {ty:?}")
            }
            Self::MemberNotFound(ty, name) => {
                write!(f, "{ty:?} has no member: {name}")
            }
            Self::CalleeNotCallable(ty) => write!(f, "Callee not callable: {ty:?}"),
            Self::TypeNotFound(string) => write!(f, "{string}"),
            Self::MissingConformanceRequirement(string) => {
                write!(f, "Missing conformance requirement: {string:?}")
            }
            Self::TypesDoesNotConform { .. } => {
                write!(f, "Type does not conform wip")
            }
        }
    }
}
