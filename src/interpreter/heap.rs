use crate::interpreter::value::Value;

#[derive(Debug)]
pub struct Heap {
    storage: Vec<Value>,
}

impl Default for Heap {
    fn default() -> Self {
        Heap {
            storage: Default::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pointer(pub usize);

impl Heap {
    pub fn new() -> Self {
        Heap::default()
    }

    pub fn alloc(&mut self) -> Pointer {
        let addr = self.storage.len();
        self.storage.push(Value::Void);
        Pointer(addr)
    }

    pub fn load(&self, pointer: &Pointer) -> Value {
        self.storage
            .get(pointer.0)
            .cloned()
            .expect("did not find value for pointer")
    }

    pub fn load_gep(&self, pointer: &Pointer, offset: usize) -> &Value {
        let value = self
            .storage
            .get(pointer.0)
            .expect("did not find value for pointer");
        match value {
            Value::Struct(values) => &values[offset],
            _ => panic!("didn't find value for gep pointer"),
        }
    }

    pub fn store_gep(&mut self, pointer: &Pointer, offset: usize, val: Value) {
        let value = self
            .storage
            .get_mut(pointer.0)
            .expect("did not find value for pointer");
        match value {
            Value::Struct(values) => {
                values[offset] = val;
            }
            _ => panic!("didn't find value for gep pointer"),
        }
    }

    pub fn store(&mut self, pointer: &Pointer, val: Value) {
        self.storage[pointer.0] = val
    }
}
