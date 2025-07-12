use crate::{
    environment::Environment,
    lowering::ir_module::IRModule,
    transforms::{
        dead_code_elimination::DeadCodeEliminator,
        monomorphizer::Monomorphizer,
        tail_call_optimization::TailCallOptimizer,
    },
};

pub struct ModulePassManager {}

impl ModulePassManager {
    pub fn run(env: &Environment, module: IRModule) -> IRModule {
        let monomorphized = Monomorphizer::new(env).run(module);
        let tco = TailCallOptimizer::new().run(monomorphized);
        DeadCodeEliminator::new().run(tco)
    }
}
