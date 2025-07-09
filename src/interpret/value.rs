use std::fmt::Display;

use crate::{
    SymbolID,
    interpret::{interpreter::InterpreterError, memory::Pointer},
};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Enum {
        tag: u16,
        values: Vec<Value>,
    },
    Void,
    Struct(SymbolID, Vec<Value>),
    Pointer(Pointer),
    Func(usize),
    RawBuffer(Vec<u8>),
    Array(Vec<Value>),
    Buffer {
        elements: Vec<Value>,
        count: usize,
        capacity: usize,
    },
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{i}"),
            Value::Float(i) => write!(f, "{i}"),
            Value::Bool(i) => write!(f, "{i}"),
            Value::Enum { tag, values } => write!(f, ".{tag}({values:?})"),
            Value::Void => write!(f, "void"),
            Value::Struct(sym, values) => {
                if *sym == SymbolID::STRING {
                    write!(
                        f,
                        "String({})",
                        values
                            .iter()
                            .map(|v| format!("{v}"))
                            .collect::<Vec<String>>()
                            .join(",")
                    )
                } else {
                    write!(
                        f,
                        "Struct({})",
                        values
                            .iter()
                            .map(|v| format!("{v}"))
                            .collect::<Vec<String>>()
                            .join(", ")
                    )
                }
            }
            Value::Pointer(pointer) => write!(f, "0x{pointer}"),
            Value::Func(func) => write!(f, "@{func:?}()"),
            Value::RawBuffer(b) => write!(f, "{b:?}"),
            Value::Array(values) => write!(
                f,
                "[{}]",
                values
                    .iter()
                    .map(|v| format!("{v}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),

            Value::Buffer { .. } => write!(f, "buf"),
        }
    }
}

impl Value {
    pub fn add(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    pub fn sub(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    pub fn mul(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    pub fn div(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a / b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    pub fn gt(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a > b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    pub fn gte(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a >= b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    pub fn lt(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a < b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    pub fn lte(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a <= b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }
}
