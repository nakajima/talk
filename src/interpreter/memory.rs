use crate::{interpreter::value::Value, lowering::ir_type::IRType};

// Simulate memory, kinda
pub struct Memory {
    storage: [Option<Value>; 1024],
}

pub struct Pointer {
    addr: usize,
}

impl Memory {
    pub fn new() -> Self {
        Self {
            storage: [const { None }; 1024],
        }
    }

    pub fn push_stack_frame() {}

    pub fn pop_stake_frame() {}

    pub fn alloc(ty: IRType, count: usize) -> Pointer {}

    pub fn store(addr: Pointer, val: Value) {}

    pub fn load(addr: Pointer) -> Value {}
}
