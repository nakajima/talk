use std::{fmt::Display, str::FromStr};

use crate::lowering::{ir_error::IRError, register::Register};

#[derive(Debug, Clone, PartialEq)]
pub enum IRValue {
    Register(Register),
    ImmediateInt(i64),
}

impl Display for IRValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Register(register) => write!(f, "{register}"),
            Self::ImmediateInt(int) => write!(f, "=i{int}"),
        }
    }
}

impl From<Register> for IRValue {
    fn from(value: Register) -> Self {
        IRValue::Register(value)
    }
}

impl From<i64> for IRValue {
    fn from(value: i64) -> Self {
        IRValue::ImmediateInt(value)
    }
}

impl FromStr for IRValue {
    type Err = IRError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.trim().chars().peekable();
        match chars.peek() {
            Some('%') => Register::from_str(s).map(|reg| Ok(Self::Register(reg)))?,
            Some('=') => {
                chars.next(); // Move past the =
                match chars.next() {
                    Some('i') => {
                        let mut string = String::new();
                        for next_char in chars {
                            string.push(next_char);
                        }
                        Ok(IRValue::ImmediateInt(
                            str::parse(&string).map_err(|_e| IRError::ParseError)?,
                        ))
                    }
                    _ => Err(IRError::ParseError),
                }
            }
            _ => Err(IRError::ParseError),
        }
    }
}
