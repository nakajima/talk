use crate::{
    environment::Environment,
    lowering::ir_module::IRModule,
    transforms::{
        constant_folding::ConstantFolder, dead_code_elimination::DeadCodeEliminator,
        monomorphizer::Monomorphizer,
    },
};

pub struct ModulePassManager {}

impl ModulePassManager {
    pub fn run(env: &Environment, module: IRModule) -> IRModule {
        let monomorphized = Monomorphizer::new(env).run(module);
        let dead_code_eliminated = DeadCodeEliminator::new().run(monomorphized);
        ConstantFolder::new().run(dead_code_eliminated)
    }
}
