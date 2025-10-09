use crate::ir::value::Value;

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub struct Register(pub u32);

impl From<u32> for Register {
    fn from(value: u32) -> Self {
        Register(value)
    }
}

impl From<Register> for Value {
    fn from(value: Register) -> Self {
        Value::Reg(value.0)
    }
}
