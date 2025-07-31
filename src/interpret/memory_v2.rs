use std::{
    ptr::NonNull,
};

use crate::{
    interpret::{interpreter_v2::InterpreterError, arena::Arena},
    lowering::{ir_module::IRConstantData, ir_type::IRType},
};

#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub size: usize,
    pub align: usize,
    pub ty: IRType,
}

#[derive(Debug, Clone)]
pub enum Value {
    Immediate(i64),
    Float(f64),
    Bool(bool),
    HeapPtr(NonNull<u8>, TypeInfo),
}

#[derive(Debug)]
pub struct Memory {
    stack: Vec<u8>,
    stack_ptr: usize,
    heap: Arena,
    static_data: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct Pointer {
    pub addr: usize,
    pub ty: IRType,
    pub location: MemoryLocation,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MemoryLocation {
    Stack,
    Heap,
    Static,
}

impl Memory {
    pub fn new(static_memory: &[IRConstantData]) -> Self {
        let mut static_data = Vec::new();
        
        for data in static_memory {
            match data {
                IRConstantData::RawBuffer(buf) => {
                    static_data.extend_from_slice(buf);
                }
            }
        }
        
        Self {
            stack: vec![0; 1024 * 1024], // 1MB stack
            stack_ptr: 0,
            heap: Arena::new(),
            static_data,
        }
    }
    
    pub fn type_info(ty: &IRType) -> TypeInfo {
        match ty {
            IRType::Int => TypeInfo {
                size: 8,
                align: 8,
                ty: ty.clone(),
            },
            IRType::Float => TypeInfo {
                size: 8,
                align: 8,
                ty: ty.clone(),
            },
            IRType::Bool => TypeInfo {
                size: 1,
                align: 1,
                ty: ty.clone(),
            },
            IRType::Byte => TypeInfo {
                size: 1,
                align: 1,
                ty: ty.clone(),
            },
            IRType::Pointer { .. } => TypeInfo {
                size: 8,
                align: 8,
                ty: ty.clone(),
            },
            IRType::Struct(_, fields, _) => {
                let mut size = 0;
                let mut max_align = 1;
                
                for field in fields {
                    let field_info = Self::type_info(field);
                    // Align to field alignment
                    size = (size + field_info.align - 1) & !(field_info.align - 1);
                    size += field_info.size;
                    max_align = max_align.max(field_info.align);
                }
                
                // Final padding for struct alignment
                size = (size + max_align - 1) & !(max_align - 1);
                
                TypeInfo {
                    size,
                    align: max_align,
                    ty: ty.clone(),
                }
            }
            IRType::TypedBuffer { element } => {
                let elem_info = Self::type_info(element);
                TypeInfo {
                    size: elem_info.size,
                    align: elem_info.align,
                    ty: ty.clone(),
                }
            }
            _ => TypeInfo {
                size: 8,
                align: 8,
                ty: ty.clone(),
            },
        }
    }
    
    pub fn stack_alloc(&mut self, ty: &IRType) -> Pointer {
        let info = Self::type_info(ty);
        
        // Align stack pointer
        self.stack_ptr = (self.stack_ptr + info.align - 1) & !(info.align - 1);
        
        let addr = self.stack_ptr;
        self.stack_ptr += info.size;
        
        if self.stack_ptr > self.stack.len() {
            panic!("Stack overflow!");
        }
        
        Pointer {
            addr,
            ty: ty.clone(),
            location: MemoryLocation::Stack,
        }
    }
    
    pub fn heap_alloc(&mut self, ty: &IRType, count: usize) -> Result<Pointer, InterpreterError> {
        let info = Self::type_info(ty);
        let total_size = info.size * count;
        
        if total_size == 0 {
            return Err(InterpreterError::Unknown("Cannot allocate 0 bytes".into()));
        }
        
        let ptr = self.heap.alloc(total_size, info.align);
        
        Ok(Pointer {
            addr: ptr.as_ptr() as usize,
            ty: ty.clone(),
            location: MemoryLocation::Heap,
        })
    }
    
    pub fn store(&mut self, pointer: &Pointer, value: Value) -> Result<(), InterpreterError> {
        let info = Self::type_info(&pointer.ty);
        
        match pointer.location {
            MemoryLocation::Stack => {
                if pointer.addr + info.size > self.stack.len() {
                    return Err(InterpreterError::Unknown("Stack overflow on store".into()));
                }
                Self::store_value_to_slice(&mut self.stack[pointer.addr..(pointer.addr + info.size)], value, &info)?;
            }
            MemoryLocation::Heap => {
                unsafe {
                    let ptr = pointer.addr as *mut u8;
                    let slice = std::slice::from_raw_parts_mut(ptr, info.size);
                    Self::store_value_to_slice(slice, value, &info)?;
                }
            }
            MemoryLocation::Static => {
                return Err(InterpreterError::Unknown("Cannot write to static memory".into()));
            }
        }
        
        Ok(())
    }
    
    pub fn load(&self, pointer: &Pointer) -> Result<Value, InterpreterError> {
        let info = Self::type_info(&pointer.ty);
        
        match pointer.location {
            MemoryLocation::Stack => {
                if pointer.addr + info.size > self.stack.len() {
                    return Err(InterpreterError::Unknown("Stack underflow on load".into()));
                }
                self.load_value_from(&self.stack[pointer.addr..], &info)
            }
            MemoryLocation::Heap => {
                unsafe {
                    let ptr = pointer.addr as *const u8;
                    let slice = std::slice::from_raw_parts(ptr, info.size);
                    self.load_value_from(slice, &info)
                }
            }
            MemoryLocation::Static => {
                if pointer.addr + info.size > self.static_data.len() {
                    return Err(InterpreterError::Unknown("Static memory out of bounds".into()));
                }
                self.load_value_from(&self.static_data[pointer.addr..], &info)
            }
        }
    }
    
    fn store_value_to_slice(slice: &mut [u8], value: Value, info: &TypeInfo) -> Result<(), InterpreterError> {
        match (&value, &info.ty) {
            (Value::Immediate(i), IRType::Int) => {
                slice[..8].copy_from_slice(&i.to_ne_bytes());
            }
            (Value::Float(f), IRType::Float) => {
                slice[..8].copy_from_slice(&f.to_ne_bytes());
            }
            (Value::Bool(b), IRType::Bool) => {
                slice[0] = if *b { 1 } else { 0 };
            }
            (Value::Immediate(i), IRType::Byte) => {
                slice[0] = *i as u8;
            }
            (Value::HeapPtr(ptr, _), IRType::Pointer { .. }) => {
                let addr = ptr.as_ptr() as usize;
                slice[..8].copy_from_slice(&addr.to_ne_bytes());
            }
            _ => {
                return Err(InterpreterError::Unknown(
                    format!("Type mismatch in store: {:?} vs {:?}", value, info.ty)
                ));
            }
        }
        Ok(())
    }
    
    fn load_value_from(&self, slice: &[u8], info: &TypeInfo) -> Result<Value, InterpreterError> {
        match &info.ty {
            IRType::Int => {
                let bytes = slice[..8].try_into()
                    .map_err(|_| InterpreterError::Unknown("Invalid load".into()))?;
                Ok(Value::Immediate(i64::from_ne_bytes(bytes)))
            }
            IRType::Float => {
                let bytes = slice[..8].try_into()
                    .map_err(|_| InterpreterError::Unknown("Invalid load".into()))?;
                Ok(Value::Float(f64::from_ne_bytes(bytes)))
            }
            IRType::Bool => {
                Ok(Value::Bool(slice[0] != 0))
            }
            IRType::Byte => {
                Ok(Value::Immediate(slice[0] as i64))
            }
            IRType::Pointer { .. } => {
                let bytes = slice[..8].try_into()
                    .map_err(|_| InterpreterError::Unknown("Invalid load".into()))?;
                let addr = usize::from_ne_bytes(bytes);
                let ptr = NonNull::new(addr as *mut u8)
                    .ok_or_else(|| InterpreterError::Unknown("Null pointer".into()))?;
                Ok(Value::HeapPtr(ptr, TypeInfo {
                    size: 8,
                    align: 8,
                    ty: info.ty.clone(),
                }))
            }
            _ => Err(InterpreterError::Unknown(
                format!("Cannot load type: {:?}", info.ty)
            )),
        }
    }
    
    pub fn reset_stack(&mut self) {
        self.stack_ptr = 0;
    }
    
    pub fn get_stack_pointer(&self) -> usize {
        self.stack_ptr
    }
    
    pub fn set_stack_pointer(&mut self, sp: usize) {
        self.stack_ptr = sp;
    }
}

