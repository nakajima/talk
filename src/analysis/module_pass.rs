use crate::lowering::ir_module::IRModule;

pub trait ModulePass {
    fn run(&self, module: &mut IRModule);
}
