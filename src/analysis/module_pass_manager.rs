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
        let folded = ConstantFolder::new().run(monomorphized);
        DeadCodeEliminator::new().run(folded)
    }
}
