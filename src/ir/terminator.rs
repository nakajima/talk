use std::fmt::Display;

use crate::ir::value::Value;

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator<T> {
    Ret { val: Value, ty: T },
    Unreachable,
}

impl<T: Display> Display for Terminator<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ret { val, ty } => write!(f, "ret {} {}", ty, val),
            Self::Unreachable => write!(f, "unreachable"),
        }
    }
}
