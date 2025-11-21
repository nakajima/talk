use std::fmt::Display;

use crate::ir::{basic_block::BasicBlockId, value::Value};

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator<T> {
    Ret {
        val: Value,
        ty: T,
    },
    Unreachable,
    Branch {
        cond: Value,
        conseq: BasicBlockId,
        alt: BasicBlockId,
    },
    Jump {
        to: BasicBlockId,
    },
}

impl<T: Display> Display for Terminator<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ret { val, ty } => write!(f, "ret {} {}", ty, val),
            Self::Branch { cond, conseq, alt } => write!(f, "br {} {} {}", cond, conseq, alt),
            Self::Jump { to } => write!(f, "jmp {to}"),
            Self::Unreachable => write!(f, "unreachable"),
        }
    }
}
