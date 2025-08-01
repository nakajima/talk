use crate::{
    SymbolID,
    interpret::{
        interpreter_v2::InterpreterError,
        memory_v2::{Memory, Pointer, Value as MemValue},
    },
    lowering::ir_type::IRType,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Pointer(Pointer),
    Struct(SymbolID, Vec<Value>),
    Enum(SymbolID, Box<Value>),
    Array(Vec<Value>),
    RawBuffer(Vec<u8>),
    Func(SymbolID),
}

impl Value {
    pub fn to_memory_value(&self) -> Result<MemValue, InterpreterError> {
        match self {
            Value::Int(i) => Ok(MemValue::Immediate(*i)),
            Value::Float(f) => Ok(MemValue::Float(*f)),
            Value::Bool(b) => Ok(MemValue::Bool(*b)),
            Value::Pointer(p) => {
                // For static pointers (like string constants), just store as immediate
                if p.location == crate::interpret::memory_v2::MemoryLocation::Static {
                    Ok(MemValue::Immediate(p.addr as i64))
                } else if p.addr == 0 {
                    // Handle null pointers as immediate 0
                    Ok(MemValue::Immediate(0))
                } else {
                    // Convert to HeapPtr for storage
                    let ptr = std::ptr::NonNull::new(p.addr as *mut u8)
                        .ok_or_else(|| InterpreterError::Unknown("Null pointer".into()))?;
                    Ok(MemValue::HeapPtr(ptr, Memory::type_info(&p.ty)))
                }
            }
            _ => Err(InterpreterError::Unknown(
                "Cannot convert complex value to memory value directly".into(),
            )),
        }
    }

    pub fn from_memory_value(mem_val: MemValue, ty: &IRType) -> Result<Self, InterpreterError> {
        match (&mem_val, ty) {
            (MemValue::Immediate(i), IRType::Int | IRType::Byte) => Ok(Value::Int(*i)),
            (MemValue::Float(f), IRType::Float) => Ok(Value::Float(*f)),
            (MemValue::Bool(b), IRType::Bool) => Ok(Value::Bool(*b)),
            (MemValue::Immediate(addr), IRType::Pointer { .. }) => {
                Ok(Value::Pointer(Pointer {
                    addr: *addr as usize,
                    ty: ty.clone(),
                    // We can't determine location from the value alone
                    // This is a limitation - we assume heap for now
                    location: crate::interpret::memory_v2::MemoryLocation::Heap,
                }))
            }
            (MemValue::HeapPtr(ptr, _), IRType::Pointer { .. }) => Ok(Value::Pointer(Pointer {
                addr: ptr.as_ptr() as usize,
                ty: ty.clone(),
                location: crate::interpret::memory_v2::MemoryLocation::Heap,
            })),
            _ => Err(InterpreterError::Unknown(format!(
                "Type mismatch converting from memory: {:?} vs {:?}",
                mem_val, ty
            ))),
        }
    }

    pub fn store_to_memory(
        &self,
        memory: &mut Memory,
        pointer: &Pointer,
    ) -> Result<(), InterpreterError> {
        match self {
            Value::Int(_) | Value::Float(_) | Value::Bool(_) | Value::Pointer(_) => {
                let mem_val = self.to_memory_value()?;
                memory.store(pointer, mem_val)
            }
            Value::Struct(_, fields) => {
                // Store struct fields sequentially
                let IRType::Struct(_, field_types, _) = &pointer.ty else {
                    return Err(InterpreterError::Unknown("Expected struct type".into()));
                };

                let mut offset = 0;
                for (field, field_ty) in fields.iter().zip(field_types.iter()) {
                    let info = Memory::type_info(field_ty);

                    // Align offset
                    offset = (offset + info.align - 1) & !(info.align - 1);

                    let field_ptr = Pointer {
                        addr: pointer.addr + offset,
                        ty: field_ty.clone(),
                        location: pointer.location,
                    };

                    field.store_to_memory(memory, &field_ptr)?;
                    offset += info.size;
                }
                Ok(())
            }
            Value::Array(elements) => {
                let IRType::TypedBuffer { element } = &pointer.ty else {
                    return Err(InterpreterError::Unknown("Expected array type".into()));
                };

                let elem_info = Memory::type_info(element);

                for (i, elem) in elements.iter().enumerate() {
                    let elem_ptr = Pointer {
                        addr: pointer.addr + i * elem_info.size,
                        ty: element.as_ref().clone(),
                        location: pointer.location,
                    };

                    elem.store_to_memory(memory, &elem_ptr)?;
                }
                Ok(())
            }
            Value::RawBuffer(bytes) => {
                // Store raw bytes directly
                for (i, &byte) in bytes.iter().enumerate() {
                    let byte_ptr = Pointer {
                        addr: pointer.addr + i,
                        ty: IRType::Byte,
                        location: pointer.location,
                    };

                    let byte_val = Value::Int(byte as i64);
                    byte_val.store_to_memory(memory, &byte_ptr)?;
                }
                Ok(())
            }
            Value::Func(sym) => {
                // Store function symbol ID as an integer
                let func_val = Value::Int(sym.0 as i64);
                func_val.store_to_memory(memory, pointer)
            }
            _ => Err(InterpreterError::Unknown(format!(
                "Cannot store value type: {:?}",
                self
            ))),
        }
    }

    pub fn load_from_memory(memory: &Memory, pointer: &Pointer) -> Result<Self, InterpreterError> {
        match &pointer.ty {
            IRType::Int | IRType::Byte => {
                let mem_val = memory.load(pointer)?;
                Self::from_memory_value(mem_val, &pointer.ty)
            }
            IRType::Float => {
                let mem_val = memory.load(pointer)?;
                Self::from_memory_value(mem_val, &pointer.ty)
            }
            IRType::Bool => {
                let mem_val = memory.load(pointer)?;
                Self::from_memory_value(mem_val, &pointer.ty)
            }
            IRType::Pointer { .. } => {
                let mem_val = memory.load(pointer)?;
                Self::from_memory_value(mem_val, &pointer.ty)
            }
            IRType::Struct(sym, field_types, _) => {
                let mut fields = Vec::new();
                let mut offset = 0;

                for field_ty in field_types {
                    let info = Memory::type_info(field_ty);

                    // Align offset
                    offset = (offset + info.align - 1) & !(info.align - 1);

                    let field_ptr = Pointer {
                        addr: pointer.addr + offset,
                        ty: field_ty.clone(),
                        location: pointer.location,
                    };

                    fields.push(Self::load_from_memory(memory, &field_ptr)?);
                    offset += info.size;
                }

                Ok(Value::Struct(*sym, fields))
            }
            _ => Err(InterpreterError::Unknown(format!(
                "Cannot load type: {:?}",
                pointer.ty
            ))),
        }
    }

    pub fn display<F>(&self, symbol_name: &F) -> String
    where
        F: Fn(SymbolID) -> String,
    {
        match self {
            Value::Int(i) => i.to_string(),
            Value::Float(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Pointer(p) => format!("0x{:x}", p.addr),
            Value::Struct(sym, fields) => {
                let field_strs: Vec<String> =
                    fields.iter().map(|f| f.display(symbol_name)).collect();
                format!("{}{{ {} }}", symbol_name(*sym), field_strs.join(", "))
            }
            Value::Enum(sym, val) => {
                format!("{}({})", symbol_name(*sym), val.display(symbol_name))
            }
            Value::Array(elements) => {
                let elem_strs: Vec<String> =
                    elements.iter().map(|e| e.display(symbol_name)).collect();
                format!("[{}]", elem_strs.join(", "))
            }
            Value::RawBuffer(bytes) => {
                if bytes.iter().all(|&b| b >= 32 && b < 127) {
                    // If all bytes are printable ASCII, show as string
                    format!("\"{}\"", String::from_utf8_lossy(bytes))
                } else {
                    format!("<buffer {} bytes>", bytes.len())
                }
            }
            Value::Func(sym) => format!("<function {}>", symbol_name(*sym)),
        }
    }
}

// Arithmetic operations
impl Value {
    pub fn add(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    pub fn sub(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    pub fn mul(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    pub fn div(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => {
                if *b == 0 {
                    Err(InterpreterError::Unknown("Division by zero".into()))
                } else {
                    Ok(Value::Int(a / b))
                }
            }
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    pub fn rem(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => {
                if *b == 0 {
                    Err(InterpreterError::Unknown("Division by zero".into()))
                } else {
                    Ok(Value::Int(a % b))
                }
            }
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    // Comparison operations
    pub fn eq(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a == b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a == b)),
            (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a == b)),
            _ => Ok(Value::Bool(false)),
        }
    }

    pub fn neq(&self, other: &Value) -> Result<Value, InterpreterError> {
        self.eq(other).map(|v| match v {
            Value::Bool(b) => Value::Bool(!b),
            _ => unreachable!(),
        })
    }

    pub fn lt(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a < b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    pub fn lte(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a <= b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    pub fn gt(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a > b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    pub fn gte(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a >= b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    // Logical operations
    pub fn and(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a && *b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    pub fn or(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a || *b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                format!("{:?}", other),
            )),
        }
    }

    pub fn not(&self) -> Result<Value, InterpreterError> {
        match self {
            Value::Bool(b) => Ok(Value::Bool(!b)),
            _ => Err(InterpreterError::TypeError(
                format!("{:?}", self),
                "bool".into(),
            )),
        }
    }
}
