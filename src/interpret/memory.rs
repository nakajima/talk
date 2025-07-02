use std::ops::Add;

use crate::{
    SymbolID,
    interpret::value::Value,
    lowering::{ir_module::IRConstantData, ir_type::IRType},
};

pub const MEM_SIZE: usize = 2048;

// Simulate memory, kinda. Compound types (like structs or buffers) are laid out inline.
// The first 1024 slots are for stack, the second 1024 slots are for heap.
#[derive(Debug)]
pub struct Memory {
    storage: [Option<Value>; MEM_SIZE],
    pub next_stack_addr: usize,
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
        Self::new(&[])
    }
}

impl Memory {
    pub fn new(static_memory: &[IRConstantData]) -> Self {
        let mut memory = Self {
            storage: [const { None }; MEM_SIZE],
            next_stack_addr: 0,
            next_heap_addr: 1024,
        };

        memory.next_stack_addr = static_memory.len();
        memory.next_heap_addr = static_memory.len() + 1024;

        for (i, val) in static_memory.iter().enumerate() {
            memory.storage[i] = match val {
                IRConstantData::RawBuffer(buf) => Some(Value::RawBuffer(buf.clone())),
            }
        }

        println!("init memory: {memory:?}");

        memory
    }

    pub fn range_mut(&mut self, start: usize, length: usize) -> &mut [Option<Value>] {
        &mut self.storage[start..(start + length)]
    }

    pub fn range(&self, start: usize, length: usize) -> &[Option<Value>] {
        &self.storage[start..(start + length)]
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

    #[allow(clippy::panic)]
    #[allow(clippy::unwrap_used)]
    pub fn load(&self, pointer: &Pointer, ty: &IRType) -> Value {
        let range = pointer.addr..(pointer.addr + Self::mem_size(ty));
        #[allow(clippy::unwrap_used)]
        match ty {
            // Special case some stuff
            IRType::Struct(struct_id, _, _) => match *struct_id {
                SymbolID::STRING => {
                    println!("loading string: {range:?}");
                    let string_struct_props: Vec<Value> = self.storage[range]
                        .iter()
                        .map(|c| c.clone().unwrap())
                        .collect();

                    println!("string props: {string_struct_props:?}");

                    let Value::Int(length) = string_struct_props[0] else {
                        panic!("Didn't get length");
                    };

                    let Value::Pointer(Pointer { addr }) = string_struct_props[2] else {
                        panic!("didn't get storage")
                    };

                    let Some(Value::RawBuffer(buf)) = self.storage[addr].clone() else {
                        panic!(
                            "didn't get string storage ({addr}): {:?}",
                            self.storage[addr],
                        );
                    };

                    assert_eq!(
                        buf.len(),
                        length as usize,
                        "string buffer/length mismatch: {buf:?}"
                    );

                    Value::String(String::from_utf8(buf).unwrap())
                }
                _ => Value::Struct(
                    self.storage[range]
                        .iter()
                        .map(|c| c.clone().unwrap())
                        .collect(),
                ),
            },
            // Value::Enum { tag, values } => {
            //     let mut vals: Vec<Option<Value>> =
            //         values.iter().cloned().map(Option::Some).collect();
            //     vals.resize(range.into_iter().len() + 1, None);
            //     self.storage[range].clone_from_slice(&vals)
            // }
            IRType::TypedBuffer { .. } => {
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

    #[allow(clippy::panic)]
    fn mem_size(ty: &IRType) -> usize {
        match ty {
            IRType::TypeVar(var) => panic!("cannot determine size of type variable: {var:?}"),
            // IRType::Enum(vars) => vars.iter().map(|t| Self::mem_size(&t)).max().unwrap_or(0),
            IRType::Struct(_, values, _) => values.len(),
            IRType::TypedBuffer { element } => Self::mem_size(element),
            _ => 1,
        }
    }
}
