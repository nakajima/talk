use crate::{
    SymbolID,
    interpret::{
        interpreter::{IRInterpreter, InterpreterError},
        io::InterpreterIO,
        memory::Pointer,
    },
    lowering::{ir_module::IRModule, ir_type::IRType},
};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Enum {
        symbol_id: SymbolID,
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

impl Value {
    #[allow(clippy::unwrap_used)]
    pub fn to_string<IO: InterpreterIO>(&self, interpreter: &IRInterpreter<IO>) -> String {
        match self {
            Value::Int(i) => format!("{i}"),
            Value::Float(i) => format!("{i}"),
            Value::Bool(i) => format!("{i}"),
            Value::Enum { tag, values, .. } => format!(".{tag}({values:?})"),
            Value::Void => "void".to_string(),
            Value::Struct(sym, values) => {
                if *sym == SymbolID::STRING {
                    let Value::Pointer(ptr) = &values[2] else {
                        unreachable!()
                    };

                    let loaded = interpreter.memory.load_with_ty(ptr).unwrap();

                    let Value::RawBuffer(bytes) = loaded else {
                        unreachable!("didn't get raw buffer: {loaded:?}");
                    };
                    String::from_utf8(bytes).unwrap()
                } else {
                    let info = interpreter.symbols.get(sym).unwrap();
                    let ty = interpreter.symbols.types.get(sym).unwrap();

                    format!(
                        "{}({})",
                        info.name,
                        ty.properties
                            .iter()
                            .zip(values.iter())
                            .map(|(prop, value)| format!(
                                "{}: {}",
                                prop.name,
                                value.to_escaped_string(interpreter)
                            ))
                            .collect::<Vec<String>>()
                            .join(", ")
                    )
                }
            }
            Value::Pointer(pointer) => interpreter
                .memory
                .load_with_ty(pointer)
                .unwrap()
                .to_string(interpreter),
            Value::Func(func) => format!("@{func:?}()"),
            Value::RawBuffer(b) => format!("{b:?}"),
            Value::Array(values) => format!(
                "[{}]",
                values
                    .iter()
                    .map(|v| v.to_string(interpreter))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),

            Value::Buffer { .. } => "buf".to_string(),
        }
    }

    #[allow(clippy::unwrap_used)]
    pub fn to_escaped_string<IO: InterpreterIO>(&self, interpreter: &IRInterpreter<IO>) -> String {
        match self {
            Value::Pointer(pointer) => interpreter
                .memory
                .load_with_ty(pointer)
                .unwrap()
                .to_escaped_string(interpreter),
            Value::Struct(sym, values) => {
                if *sym == SymbolID::STRING {
                    let Value::Pointer(ptr) = &values[2] else {
                        unreachable!()
                    };

                    let loaded = interpreter.memory.load_with_ty(ptr).unwrap();

                    let Value::RawBuffer(bytes) = loaded else {
                        unreachable!("didn't get raw buffer: {loaded:?}");
                    };

                    format!("\"{}\"", String::from_utf8(bytes).unwrap())
                } else {
                    self.to_string(interpreter)
                }
            }
            _ => self.to_string(interpreter),
        }
    }
}

impl Value {
    pub fn add(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
            _ => Err(InterpreterError::TypeError(
                format!("{self:?}"),
                format!("{other:?}"),
            )),
        }
    }

    pub fn sub(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
            _ => Err(InterpreterError::TypeError(
                format!("{self:?}"),
                format!("{other:?}"),
            )),
        }
    }

    pub fn mul(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
            _ => Err(InterpreterError::TypeError(
                format!("{self:?}"),
                format!("{other:?}"),
            )),
        }
    }

    pub fn div(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a / b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
            _ => Err(InterpreterError::TypeError(
                format!("{self:?}"),
                format!("{other:?}"),
            )),
        }
    }

    pub fn gt(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a > b)),
            _ => Err(InterpreterError::TypeError(
                format!("{self:?}"),
                format!("{other:?}"),
            )),
        }
    }

    pub fn gte(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a >= b)),
            _ => Err(InterpreterError::TypeError(
                format!("{self:?}"),
                format!("{other:?}"),
            )),
        }
    }

    pub fn lt(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a < b)),
            _ => Err(InterpreterError::TypeError(
                format!("{self:?}"),
                format!("{other:?}"),
            )),
        }
    }

    pub fn lte(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a <= b)),
            _ => Err(InterpreterError::TypeError(
                format!("{self:?}"),
                format!("{other:?}"),
            )),
        }
    }

    pub fn ty(&self, module: &IRModule) -> IRType {
        match self {
            Value::Int(_) => IRType::Int,
            Value::Float(_) => IRType::Float,
            Value::Bool(_) => IRType::Bool,
            Value::Enum {
                symbol_id, values, ..
            } => IRType::Enum(*symbol_id, values.iter().map(|v| v.ty(module)).collect()),
            Value::Void => IRType::Void,
            Value::Struct(symbol_id, values) => IRType::Struct(
                *symbol_id,
                values.iter().map(|v| v.ty(module)).collect(),
                vec![],
            ),
            Value::Pointer(_) => IRType::POINTER,
            Value::Func(idx) => module.functions[*idx].ty.clone(),
            Value::RawBuffer(_) => IRType::RawBuffer,
            Value::Array(v) => {
                IRType::array(v.first().map(|v| v.ty(module)).unwrap_or(IRType::Void))
            }
            Value::Buffer { elements, .. } => IRType::TypedBuffer {
                element: elements
                    .first()
                    .map(|v| v.ty(module))
                    .unwrap_or(IRType::Void)
                    .into(),
            },
        }
    }
}
