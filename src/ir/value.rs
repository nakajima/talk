use std::str::FromStr;

use itertools::Itertools;

use crate::{
    ir::{ir_error::IRError, list::List, register::Register},
    name_resolution::symbol::Symbol,
};

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Reference {
    Func(Symbol),
    Closure(Symbol, List<Value>),
    Register { frame: usize, register: Register },
}

#[derive(Debug, Clone, Copy, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Addr(pub(super) usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum RecordId {
    Nominal(Symbol),
    Record(u32),
    Anon,
}

#[derive(Default, Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Value {
    Reg(u32),
    Int(i64),
    Float(f64),
    Func(Symbol),
    Closure {
        func: Symbol,
        env: List<Value>,
    },
    Bool(bool),
    Ref(Reference),
    Capture {
        depth: usize,
        reg: Register,
    },
    Record(RecordId, Vec<Value>),
    RawPtr(Addr),
    RawBuffer(Vec<u8>),
    Void,
    #[default]
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

    #[allow(clippy::unwrap_used)]
    pub fn as_bytes(&self) -> Vec<u8> {
        match self {
            Value::Int(v) => v.to_le_bytes().to_vec(),
            Value::Float(v) => v.to_le_bytes().to_vec(),
            Value::Func(v) => v.as_bytes().to_vec(),
            Value::Bool(v) => {
                if *v {
                    vec![1u8]
                } else {
                    vec![0u8]
                }
            }
            Value::Record(.., values) => values.iter().flat_map(|v| v.as_bytes()).collect_vec(),
            Value::RawPtr(v) => (v.0 as u64).to_le_bytes().to_vec(),
            Value::RawBuffer(bytes) => bytes.to_vec(),
            other => unreachable!("Cannot serialize {other:?}"),
        }
    }
}

impl Addr {
    pub fn offset(self, offset: usize) -> Self {
        Addr(self.0 + offset)
    }
}

impl Value {
    /// Offset all RawPtr addresses by the given amount.
    /// Used when merging static memory from imported modules.
    pub fn offset_ptrs(&mut self, offset: usize) {
        match self {
            Value::RawPtr(addr) => *addr = addr.offset(offset),
            Value::Record(_, fields) => {
                for field in fields {
                    field.offset_ptrs(offset);
                }
            }
            Value::Closure { env, .. } => {
                for val in &mut env.items {
                    val.offset_ptrs(offset);
                }
            }
            _ => {}
        }
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

        if s == "void" || s == "()" {
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
            Value::Capture { depth, reg } => write!(f, "%{reg}^{depth}"),
            Value::Ref(reference) => write!(f, "&{reference:?}"),
            Value::Reg(reg) => write!(f, "%{reg}"),
            Value::RawBuffer(v) => write!(f, "[{v:?}]"),
            Value::Record(sym, fields) => write!(f, "{sym:?}{{ {:?} }}", fields),
            Value::Int(i) => write!(f, "{i}"),
            Value::Float(i) => write!(f, "{i}"),
            Value::Func(name) => write!(f, "{}()", name),
            Value::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            Value::Closure { func, env } => write!(f, "{func}[{env}]()"),
            Value::Void => write!(f, "()"),
            Value::Uninit => write!(f, "uninit"),
            Value::Poison => write!(f, "poison"),
            Value::RawPtr(val) => write!(f, "rawptr({})", val.0),
        }
    }
}
