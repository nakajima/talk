use std::str::FromStr;

use crate::ir::{ir_error::IRError, value::Value};

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub struct Register(pub u32);

impl From<u32> for Register {
    fn from(value: u32) -> Self {
        Register(value)
    }
}

impl From<Register> for Value {
    fn from(value: Register) -> Self {
        Value::Reg(value.0)
    }
}

impl FromStr for Register {
    type Err = IRError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(str::parse::<u32>(&s[1..])
            .map_err(|e| IRError::CouldNotParse(format!("{e:?}")))?
            .into())
    }
}
