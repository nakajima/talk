use std::str::FromStr;

use crate::{
    ir::{ir_error::IRError, register::Register},
    name::Name,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Reg(u32),
    Int(i64),
    Float(f64),
    Func(Name),
    Bool(bool),
    Void,
    Uninit,
    Poison,
}

impl Value {
    pub fn as_register(&self) -> Result<Register, IRError> {
        if let Value::Reg(i) = self {
            return Ok(Register(*i));
        }

        Err(IRError::InvalidValueConversion(format!(
            "Cannot convert {self:?} to register"
        )))
    }
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

        if s == "true" {
            return Ok(Self::Bool(true));
        }

        if s == "false" {
            return Ok(Self::Bool(false));
        }

        if s == "void" {
            return Ok(Self::Void);
        }

        Ok(Self::Int(str::parse(s).map_err(|e| {
            IRError::CouldNotParse(format!("Value: {e:?}"))
        })?))
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Value::Int(value)
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Value::Float(value)
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Reg(reg) => write!(f, "%{reg}"),
            Value::Int(i) => write!(f, "{i}"),
            Value::Float(i) => write!(f, "{i}"),
            Value::Func(name) => write!(f, "@{}", name.name_str()),
            Value::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            Value::Void => write!(f, "void"),
            Value::Uninit => write!(f, "uninit"),
            Value::Poison => write!(f, "poison"),
        }
    }
}
