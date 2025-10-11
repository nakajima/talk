use std::str::FromStr;

use crate::{ir::ir_error::IRError, name::Name};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Reg(u32),
    Int(i64),
    Float(f64),
    Func(Name),
    Void,
}

impl FromStr for Value {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(s) = s.trim().strip_prefix("%") {
            return Ok(Self::Reg(str::parse(s).map_err(|e| {
                IRError::CouldNotParse(format!("Value::Reg: {e:?}"))
            })?));
        }

        if s.contains(".") {
            return Ok(Self::Float(
                str::parse(s).map_err(|e| IRError::CouldNotParse(format!("Value: {e:?}")))?,
            ));
        }

        if s == "void" {
            return Ok(Self::Void);
        }

        Ok(Self::Int(str::parse(s).map_err(|e| {
            IRError::CouldNotParse(format!("Value: {e:?}"))
        })?))
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Reg(reg) => write!(f, "%{reg}"),
            Value::Int(i) => write!(f, "{i}"),
            Value::Float(i) => write!(f, "{i}"),
            Value::Func(name) => write!(f, "@{}", name.name_str()),
            Value::Void => write!(f, "void"),
        }
    }
}
