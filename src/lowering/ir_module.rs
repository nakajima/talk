use crate::lowering::ir_function::IRFunction;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum IRConstantData {
    RawBuffer(Vec<u8>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
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
