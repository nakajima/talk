use crate::lowering::lowerer::IRFunction;

pub struct IRModule {
    pub functions: Vec<IRFunction>,
}

impl IRModule {
    pub fn new() -> Self {
        Self {
            functions: Default::default(),
        }
    }
}
