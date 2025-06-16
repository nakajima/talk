use crate::{
    interpreter::{heap::Pointer, interpreter::InterpreterError},
    lowering::ir_type::IRType,
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
    Struct(Vec<Value>),
    Pointer(Pointer),
    Func(Pointer),
    Array {
        elements: Vec<Value>,
        count: usize,
        capacity: usize,
    },
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
            IRType::Struct(_, irtypes) => {
                let mut start = 0;
                let mut members = vec![];
                for ty in irtypes {
                    members.push(Value::from_bytes(
                        &bytes[start..(start + ty.mem_size())],
                        ty,
                    ));
                    start += ty.mem_size();
                }
                Value::Struct(members)
            }
            IRType::Pointer => {
                Value::Pointer(Pointer(usize::from_le_bytes(bytes.try_into().unwrap())))
            }
            IRType::Array { element } => {
                let mut buf = [0u8; 8];
                buf.copy_from_slice(&bytes[0..7]);
                let capacity = usize::from_le_bytes(buf);
                buf.copy_from_slice(&bytes[8..15]);
                let count = usize::from_le_bytes(buf);
                let mut elements: Vec<Value> = vec![];
                for el_bytes in bytes[16..].chunks_exact(element.mem_size()) {
                    elements.push(Value::from_bytes(el_bytes, element));
                }

                Value::Array {
                    elements,
                    count,
                    capacity,
                }
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
            Value::Struct(values) => {
                let mut bytes = vec![];
                for value in values {
                    bytes.extend(value.as_bytes());
                }
                bytes
            }
            Value::Pointer(pointer) => pointer.0.to_le_bytes().to_vec(),
            Value::Func(id) => id.0.to_le_bytes().to_vec(),
            Value::Array {
                elements,
                count,
                capacity,
            } => {
                let mut bytes = capacity.to_le_bytes().to_vec();
                bytes.extend(count.to_le_bytes());
                bytes.extend(
                    elements
                        .iter()
                        .flat_map(Value::as_bytes)
                        .collect::<Vec<u8>>(),
                );
                bytes
            }
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
