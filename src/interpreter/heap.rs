use crate::{interpreter::value::Value, lowering::ir_type::IRType};

#[derive(Debug)]
pub struct Heap {
    bytes: Vec<u8>,
    next_free_addr: usize,
    capacity: usize,
}

impl Default for Heap {
    fn default() -> Self {
        Heap {
            bytes: vec![0, 0, 0, 0],
            next_free_addr: 0,
            capacity: 4,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pointer(pub usize);

impl Heap {
    pub fn new() -> Self {
        Heap::default()
    }

    pub fn alloc(&mut self, ty: &IRType) -> Pointer {
        if self.next_free_addr + ty.mem_size() > self.capacity {
            log::trace!(
                "Need more memory for {:?} {:?}. Allocating",
                ty,
                ty.mem_size()
            );
            let new_capacity = (self.capacity + ty.mem_size()) * 2;
            self.bytes.resize(new_capacity, 0);
            self.capacity = new_capacity;
            log::trace!("New capacity is {:?}", new_capacity);
        }

        let addr = self.next_free_addr;
        log::trace!("Allocating {:?} at {:?}", ty, addr);
        self.next_free_addr += ty.mem_size();
        log::trace!("Next free addr is {:?}", self.next_free_addr);
        Pointer(addr)
    }

    pub fn load(&mut self, pointer: &Pointer, ty: &IRType) -> Value {
        let byte_range = pointer.0..(pointer.0 + ty.mem_size());
        Value::from_bytes(&self.bytes[byte_range], ty)
    }

    pub fn store(&mut self, pointer: &Pointer, val: &Value, ty: &IRType) {
        let byte_range = pointer.0..(pointer.0 + ty.mem_size());
        log::trace!(
            "Storing value {:?} {:?} of type {:?} at {:?} in {:?}",
            pointer,
            val,
            ty,
            byte_range,
            self.bytes
        );
        self.bytes[byte_range].copy_from_slice(&val.as_bytes());
    }
}
