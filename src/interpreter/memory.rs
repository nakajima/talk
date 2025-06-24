use std::ops::Add;

use crate::{interpreter::value::Value, lowering::ir_type::IRType};

pub const MEM_SIZE: usize = 2048;

// pub static mut MEMORY: [Option<Value>; MEM_SIZE] = [const { None }; MEM_SIZE];

// Simulate memory, kinda. Compound types (like structs or buffers) are laid out inline.
// The first 1024 slots are for stack, the second 1024 slots are for heap.
pub struct Memory {
    storage: [Option<Value>; MEM_SIZE],
    next_stack_addr: usize,
    next_heap_addr: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pointer {
    addr: usize,
}

impl Add<usize> for Pointer {
    type Output = Pointer;

    fn add(self, rhs: usize) -> Self::Output {
        Pointer {
            addr: self.addr + rhs,
        }
    }
}

impl Pointer {
    pub fn new(addr: usize) -> Self {
        Self { addr }
    }
}

impl Default for Memory {
    fn default() -> Self {
        Self::new()
    }
}

impl Memory {
    pub fn new() -> Self {
        Self {
            storage: [const { None }; MEM_SIZE],
            next_stack_addr: 0,
            next_heap_addr: 1024,
        }
    }

    pub fn range_mut(&mut self, start: usize, length: usize) -> &mut [Option<Value>] {
        &mut self.storage[start..(start + length)]
    }

    pub fn range(&self, start: usize, length: usize) -> &[Option<Value>] {
        &self.storage[start..(start + length)]
    }

    pub fn set_stack_pointer(&mut self, pointer: Pointer) {
        self.next_stack_addr = pointer.addr;
    }

    pub fn stack_alloc(&mut self, ty: &IRType) -> Pointer {
        let ret = Pointer {
            addr: self.next_stack_addr,
        };
        self.next_stack_addr += Self::mem_size(ty);
        ret
    }

    pub fn heap_alloc(&mut self, ty: &IRType, count: usize) -> Pointer {
        let ret = Pointer {
            addr: self.next_heap_addr,
        };
        self.next_heap_addr += Self::mem_size(ty) * count;
        ret
    }

    pub fn store(&mut self, pointer: Pointer, val: Value, ty: &IRType) {
        let range = pointer.addr..(pointer.addr + Self::mem_size(ty));
        match val {
            Value::Struct(vals) => {
                let vals: Vec<Option<Value>> = vals.iter().cloned().map(Option::Some).collect();
                println!("----- storing struct vals {vals:?} at {range:?}");
                self.storage[range].clone_from_slice(&vals)
            }
            // Value::Enum { tag, values } => {
            //     let mut vals: Vec<Option<Value>> =
            //         values.iter().cloned().map(Option::Some).collect();
            //     vals.resize(range.into_iter().len() + 1, None);
            //     self.storage[range].clone_from_slice(&vals)
            // }
            Value::Buffer { elements, .. } => {
                let elements: Vec<Option<Value>> =
                    elements.iter().cloned().map(Option::Some).collect();
                self.storage[range].clone_from_slice(&elements);
            }
            _ => {
                self.storage[pointer.addr] = Some(val);
            }
        };
    }

    pub fn load(&self, pointer: &Pointer, ty: &IRType) -> Value {
        let range = pointer.addr..(pointer.addr + Self::mem_size(ty));
        match ty {
            IRType::Struct(_, _, _) => Value::Struct(
                self.storage[range]
                    .iter()
                    .map(|c| c.clone().unwrap())
                    .collect(),
            ),
            // Value::Enum { tag, values } => {
            //     let mut vals: Vec<Option<Value>> =
            //         values.iter().cloned().map(Option::Some).collect();
            //     vals.resize(range.into_iter().len() + 1, None);
            //     self.storage[range].clone_from_slice(&vals)
            // }
            IRType::Array { .. } => {
                let elements: Vec<Value> = self.storage[range]
                    .iter()
                    .map(|c| c.clone().unwrap())
                    .collect();
                Value::Buffer {
                    elements: elements.clone(),
                    count: elements.len(),
                    capacity: elements.len(),
                }
            }
            _ => self.storage[pointer.addr].clone().unwrap(),
        }
    }

    fn mem_size(ty: &IRType) -> usize {
        match ty {
            IRType::TypeVar(var) => panic!("cannot determine size of type variable: {var:?}"),
            // IRType::Enum(vars) => vars.iter().map(|t| Self::mem_size(&t)).max().unwrap_or(0),
            IRType::Struct(_, values, _) => values.len(),
            IRType::Array { element } => Self::mem_size(element),
            _ => 1,
        }
    }
}
