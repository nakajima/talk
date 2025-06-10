use crate::lowering::lowerer::IRFunction;

#[derive(Debug)]
pub struct IRModule {
    pub functions: Vec<IRFunction>,
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
        }
    }
}
