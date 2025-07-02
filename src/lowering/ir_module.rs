use crate::lowering::ir_function::IRFunction;

#[derive(Debug, Clone, PartialEq)]
pub enum IRConstantData {
    RawBuffer(Vec<u8>),
}

#[derive(Debug, Clone)]
pub struct IRModule {
    pub functions: Vec<IRFunction>,
    pub constants: Vec<IRConstantData>,
}

impl Default for IRModule {
    fn default() -> Self {
        Self::new()
    }
}

impl IRModule {
    pub fn new() -> Self {
        Self {
            functions: Default::default(),
            constants: Default::default(),
        }
    }
}
