use crate::lowering::{
    instr::{Callee, Instr},
    ir_function::IRFunction,
    ir_module::IRModule,
    ir_value::IRValue,
    lowerer::BasicBlockID,
    register::Register,
};

#[derive(Default)]
pub struct TailCallOptimizer;

impl TailCallOptimizer {
    pub fn new() -> Self {
        Self
    }

    pub fn run(self, mut module: IRModule) -> IRModule {
        for func in module.functions.iter_mut() {
            Self::optimize_function(func);
        }
        module
    }

    fn optimize_function(func: &mut IRFunction) {
        if func.blocks.is_empty() {
            return;
        }

        // Determine the registers for parameters (and env if present)
        let mut param_regs = Vec::new();
        if let Some(env) = func.env_reg {
            param_regs.push(env);
        }
        let offset = param_regs.len() as i32;
        for i in 0..func.args().len() {
            param_regs.push(Register(i as i32 + offset));
        }

        for block in &mut func.blocks {
            if block.instructions.len() < 2 {
                continue;
            }
            let len = block.instructions.len();
            let (call, ret) = (&block.instructions[len - 2], &block.instructions[len - 1]);
            if let (
                Instr::Call {
                    dest_reg,
                    callee: Callee::Name(name),
                    args,
                    ty,
                },
                Instr::Ret(ret_ty, Some(IRValue::Register(ret_reg))),
            ) = (call, ret)
            {
                if name == &func.name && dest_reg == ret_reg && ty == ret_ty && args.0.len() == param_regs.len() {
                    // Replace tail call with argument stores and jump to entry
                    let mut new_instrs = Vec::new();
                    for (arg, dst) in args.0.iter().zip(param_regs.iter()) {
                        new_instrs.push(Instr::StoreLocal(*dst, arg.ty.clone(), arg.register));
                    }
                    new_instrs.push(Instr::Jump(BasicBlockID::ENTRY));
                    block.instructions.truncate(len - 2);
                    block.instructions.extend(new_instrs);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::TailCallOptimizer;
    use crate::{
        assert_lowered_function,
        lowering::{
            instr::{Callee, Instr},
            ir_function::IRFunction,
            ir_module::IRModule,
            ir_type::IRType,
            ir_value::IRValue,
            lowerer::{BasicBlock, BasicBlockID, RegisterList, TypedRegister},
            register::Register,
        },
    };

    #[test]
    fn optimizes_simple_tail_call() {
        let func = IRFunction {
            debug_info: Default::default(),
            name: "@foo".into(),
            ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
            blocks: vec![BasicBlock {
                id: BasicBlockID::ENTRY,
                instructions: vec![
                    Instr::ConstantInt(Register(1), 1),
                    Instr::Sub(Register(2), IRType::Int, Register(0), Register(1)),
                    Instr::Call {
                        dest_reg: Register(3),
                        ty: IRType::Int,
                        callee: Callee::Name("@foo".into()),
                        args: RegisterList(vec![TypedRegister::new(IRType::Int, Register(2))]),
                    },
                    Instr::Ret(IRType::Int, Some(IRValue::Register(Register(3)))),
                ],
            }],
            env_ty: None,
            env_reg: None,
            size: 4,
        };

        let module = IRModule {
            functions: vec![func],
            constants: vec![],
        };

        let optimized = TailCallOptimizer::new().run(module);

        assert_lowered_function!(
            optimized,
            "@foo",
            IRFunction {
                debug_info: Default::default(),
                name: "@foo".into(),
                ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 1),
                        Instr::Sub(Register(2), IRType::Int, Register(0), Register(1)),
                        Instr::StoreLocal(Register(0), IRType::Int, Register(2)),
                        Instr::Jump(BasicBlockID::ENTRY),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 4,
            }
        );
    }
}

