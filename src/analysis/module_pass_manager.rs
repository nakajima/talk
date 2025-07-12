use crate::{
    environment::Environment,
    lowering::ir_module::IRModule,
    transforms::{dead_code_elimination::DeadCodeEliminator, monomorphizer::Monomorphizer},
};

pub struct ModulePassManager {}

impl ModulePassManager {
    pub fn run(env: &Environment, module: IRModule) -> IRModule {
        let monomorphized = Monomorphizer::new(env).run(module);
        DeadCodeEliminator::new().run(monomorphized)
    }
}
