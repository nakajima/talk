use std::{fmt::Display, str::FromStr};

use crate::ir::{basic_block::BasicBlockId, ir_error::IRError, ir_ty::IrTy, value::Value};

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

impl FromStr for Terminator<IrTy> {
    type Err = IRError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parts = s.split_whitespace();
        match parts.next() {
            Some("ret") => {
                if let Some(ty) = parts.next()
                    && let Some(val) = parts.next()
                {
                    let ty = IrTy::from_str(ty)?;
                    let val = Value::from_str(val)?;
                    return Ok(Terminator::Ret { val, ty });
                }
            }
            Some("br") => {
                if let Some(cond) = parts.next()
                    && let Some(conseq) = parts.next()
                    && let Some(alt) = parts.next()
                {
                    let cond = Value::from_str(cond)?;
                    let conseq = BasicBlockId::from_str(conseq)?;
                    let alt = BasicBlockId::from_str(alt)?;
                    return Ok(Terminator::Branch { cond, conseq, alt });
                }
            }
            Some("jmp") => {
                if let Some(to) = parts.next() {
                    println!("to: {to:?}");
                    let to = BasicBlockId::from_str(to)?;
                    return Ok(Terminator::Jump { to });
                }
            }
            Some("unreachable") => return Ok(Terminator::Unreachable),
            _ => return Err(IRError::CouldNotParse("invalid terminator syntax".into())),
        }

        return Err(IRError::CouldNotParse("invalid terminator syntax".into()));
    }
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
