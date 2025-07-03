use crate::interpret::{interpreter::InterpreterError, memory::Pointer};

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
    Struct(Vec<Value>),
    Pointer(Pointer),
    Func(usize),
    RawBuffer(Vec<u8>),
    String(String),
    Array(Vec<Value>),
    Buffer {
        elements: Vec<Value>,
        count: usize,
        capacity: usize,
    },
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
