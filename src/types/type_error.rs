use std::{error::Error, fmt::Display};

use crate::{name_resolution::symbol::TypeId, types::ty::Ty};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    TypeConstructorNotFound(TypeId),
    GenericArgCount { expected: u8, actual: u8 },
    InvalidUnification(Ty, Ty),
    OccursCheck(Ty),
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
        }
    }
}
