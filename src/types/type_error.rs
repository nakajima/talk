use std::{error::Error, fmt::Display};

use crate::{
    name::Name,
    name_resolution::symbol::{ProtocolId, Symbol},
    types::infer_ty::InferTy,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeError {
    TypeConstructorNotFound(Symbol),
    ExpectedRow(InferTy),
    GenericArgCount {
        expected: u8,
        actual: u8,
    },
    InvalidUnification(Box<InferTy>, Box<InferTy>),
    OccursCheck(InferTy),
    CalleeNotCallable(InferTy),
    MemberNotFound(InferTy, String),
    NameNotResolved(Name),
    MissingConformanceRequirement(String),
    TypeNotFound(String),
    TypesDoesNotConform {
        symbol: Symbol,
        protocol_id: ProtocolId,
    },
    TypesCannotConform {
        ty: InferTy,
        protocol_id: ProtocolId,
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
            Self::TypesCannotConform { ty, .. } => {
                write!(f, "Type cannot conform: {ty:?}")
            }
            Self::NameNotResolved(name) => {
                write!(f, "Name not resolved: {name:?}")
            }
        }
    }
}
