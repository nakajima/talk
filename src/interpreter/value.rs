use crate::{
    interpreter::{heap::Pointer, interpreter::InterpreterError},
    lowering::ir_type::IRType,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Enum { tag: u16, values: Vec<Value> },
    Void,
    Struct(Vec<Value>),
    Pointer(Pointer),
    Func(Pointer),
}

impl Value {
    pub fn from_bytes(bytes: &[u8], ty: &IRType) -> Value {
        match ty {
            IRType::Bool => {
                if bytes[0] == 1 {
                    Value::Bool(true)
                } else {
                    Value::Bool(false)
                }
            }
            IRType::Void => Value::Void,
            IRType::Int => Value::Int(i64::from_le_bytes(bytes.try_into().unwrap())),
            IRType::Float => Value::Float(f64::from_le_bytes(bytes.try_into().unwrap())),
            IRType::Func(_, _) => {
                Value::Func(Pointer(usize::from_le_bytes(bytes.try_into().unwrap())))
            }
            IRType::TypeVar(_) => todo!(),
            IRType::Enum(irtypes) => {
                let tag = u16::from_le_bytes(bytes[0..2].try_into().unwrap());
                let values = irtypes
                    .iter()
                    .map(|ty| Value::from_bytes(&bytes[2..], ty))
                    .collect();
                Value::Enum { tag, values }
            }
            IRType::Struct(irtypes) => Value::Struct(
                irtypes
                    .iter()
                    .map(|ty| Value::from_bytes(&bytes[2..], ty))
                    .collect(),
            ),
            IRType::Pointer => {
                Value::Pointer(Pointer(usize::from_le_bytes(bytes.try_into().unwrap())))
            }
        }
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        match self {
            Value::Int(int) => int.to_le_bytes().to_vec(),
            Value::Float(float) => float.to_le_bytes().to_vec(),
            Value::Bool(bool) => {
                if *bool {
                    vec![1]
                } else {
                    vec![0]
                }
            }
            Value::Enum { .. } => todo!(),
            Value::Void => todo!(),
            Value::Struct(values) => values.iter().flat_map(|v| v.as_bytes()).collect(),
            Value::Pointer(pointer) => pointer.0.to_le_bytes().to_vec(),
            Value::Func(id) => id.0.to_le_bytes().to_vec(),
        }
    }

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
