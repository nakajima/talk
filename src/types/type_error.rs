use std::{error::Error, fmt::Display};

use crate::name_resolution::symbol::DeclId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    TypeConstructorNotFound(DeclId),
    GenericArgCount { expected: u8, actual: u8 },
}

impl Error for TypeError {}
impl Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeConstructorNotFound(id) => write!(f, "Type constructor not found: {id:?}"),
            Self::GenericArgCount { expected, actual } => {
                write!(f, "Expected {expected} type arguments, got {actual}")
            }
        }
    }
}
