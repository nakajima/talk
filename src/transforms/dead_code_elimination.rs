use std::collections::{HashMap, HashSet, VecDeque};

use crate::lowering::{
    instr::{Callee, Instr},
    ir_function::IRFunction,
    ir_module::IRModule,
    lowerer::BasicBlockID,
};

/// Eliminates unreachable functions and basic blocks from an [`IRModule`].
///
/// The entry point of the program is assumed to be a function named `@main`.
/// All functions reachable from `@main` (through direct calls or function
/// references) are retained. Unreachable functions are removed. Each remaining
/// function has unreachable basic blocks pruned.
#[derive(Default)]
pub struct DeadCodeEliminator;

impl DeadCodeEliminator {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn run(self, mut module: IRModule) -> IRModule {
        let functions: HashMap<String, IRFunction> = module
            .functions
            .into_iter()
            .map(|f| (f.name.clone(), f))
            .collect();

        let mut reachable = HashSet::new();
        let mut worklist = VecDeque::new();

        if functions.contains_key("@main") {
            worklist.push_back("@main".to_string());
        }

        while let Some(name) = worklist.pop_front() {
            if !reachable.insert(name.clone()) {
                continue;
            }
            if let Some(func) = functions.get(&name) {
                for block in &func.blocks {
                    for instr in &block.instructions {
                        match instr {
                            Instr::Call {
                                callee: Callee::Name(n),
                                ..
                            } => {
                                if functions.contains_key(n) {
                                    worklist.push_back(n.clone());
                                }
                            }
                            Instr::Ref(_, _, crate::lowering::lowerer::RefKind::Func(n)) => {
                                if functions.contains_key(n) {
                                    worklist.push_back(n.clone());
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }

        let mut new_functions = Vec::new();
        for (name, mut func) in functions.into_iter() {
            if reachable.contains(&name) {
                Self::prune_blocks(&mut func);
                Self::prune_unread_registers(&mut func);
                new_functions.push(func);
            }
        }

        module.functions = new_functions;
        module
    }

    fn prune_blocks(func: &mut IRFunction) {
        if func.blocks.is_empty() {
            return;
        }
        let mut reachable = HashSet::new();
        let mut worklist = VecDeque::new();
        worklist.push_back(func.blocks[0].id);

        while let Some(id) = worklist.pop_front() {
            if !reachable.insert(id) {
                continue;
            }
            if let Some(block) = func.blocks.iter().find(|b| b.id == id)
                && let Some(term) = block.instructions.last()
            {
                for succ in term.successors() {
                    worklist.push_back(succ);
                }
            }
        }

        func.blocks.retain(|b| reachable.contains(&b.id));

        // Renumber block IDs to keep them dense
        let mut map = HashMap::new();
        for (i, block) in func.blocks.iter_mut().enumerate() {
            let new_id = BasicBlockID(i as u32);
            map.insert(block.id, new_id);
            block.id = new_id;
        }
        for block in &mut func.blocks {
            for instr in &mut block.instructions {
                match instr {
                    Instr::Jump(target) => {
                        *target = map[target];
                    }
                    Instr::Branch {
                        true_target,
                        false_target,
                        ..
                    } => {
                        *true_target = map[true_target];
                        *false_target = map[false_target];
                    }
                    Instr::Phi(_, _, predecessors) => {
                        for (_, block_id) in &mut predecessors.0 {
                            *block_id = map[block_id];
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    fn prune_unread_registers(func: &mut IRFunction) {
        let mut used = HashSet::new();

        // Gather initial set of used registers
        for block in &func.blocks {
            for instr in &block.instructions {
                for reg in instr.read_regs() {
                    used.insert(reg);
                }
            }
        }

        let mut changed = true;
        while changed {
            changed = false;
            for block in &mut func.blocks {
                let mut new_instrs = Vec::new();
                for instr in std::mem::take(&mut block.instructions) {
                    if let Some(dest) = instr.dest()
                        && !used.contains(&dest)
                        && instr.is_pure()
                    {
                        changed = true;
                        continue;
                    }
                    new_instrs.push(instr);
                }
                block.instructions = new_instrs;
            }

            if changed {
                used.clear();
                for block in &func.blocks {
                    for instr in &block.instructions {
                        for reg in instr.read_regs() {
                            used.insert(reg);
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::DeadCodeEliminator;
    use crate::lowering::{
        instr::{Callee, Instr},
        ir_function::IRFunction,
        ir_module::IRModule,
        ir_type::IRType,
        lowerer::{BasicBlock, BasicBlockID, RegisterList, TypedRegister},
        register::Register,
    };

    #[test]
    fn removes_unreachable_functions() {
        let used = IRFunction {
            debug_info: Default::default(),
            name: "@used".into(),
            ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
            blocks: vec![BasicBlock {
                id: BasicBlockID::ENTRY,
                instructions: vec![Instr::Ret(IRType::Int, Some(Register(0).into()))],
            }],
            env_ty: None,
            env_reg: None,
            size: 1,
        };
        let dead = IRFunction {
            debug_info: Default::default(),
            name: "@dead".into(),
            ty: IRType::Func(vec![], IRType::Void.into()),
            blocks: vec![BasicBlock {
                id: BasicBlockID::ENTRY,
                instructions: vec![Instr::Unreachable],
            }],
            env_ty: None,
            env_reg: None,
            size: 1,
        };
        let main = IRFunction {
            debug_info: Default::default(),
            name: "@main".into(),
            ty: IRType::Func(vec![], IRType::Void.into()),
            blocks: vec![BasicBlock {
                id: BasicBlockID::ENTRY,
                instructions: vec![Instr::Call {
                    dest_reg: Register(1),
                    ty: IRType::Int,
                    callee: Callee::Name("@used".into()),
                    args: RegisterList(vec![TypedRegister::new(IRType::Int, Register(0))]),
                }],
            }],
            env_ty: None,
            env_reg: None,
            size: 2,
        };

        let module = IRModule {
            functions: vec![main, used, dead],
            constants: vec![],
        };

        let optimized = DeadCodeEliminator::new().run(module);

        assert!(optimized.functions.iter().any(|f| f.name == "@used"));
        assert!(optimized.functions.iter().any(|f| f.name == "@main"));
        assert!(!optimized.functions.iter().any(|f| f.name == "@dead"));
    }

    #[test]
    fn removes_unreachable_blocks() {
        let func = IRFunction {
            debug_info: Default::default(),
            name: "@main".into(),
            ty: IRType::Func(vec![], IRType::Void.into()),
            blocks: vec![
                BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![Instr::Jump(BasicBlockID(1))],
                },
                BasicBlock {
                    id: BasicBlockID(1),
                    instructions: vec![Instr::Ret(IRType::Void, None)],
                },
                BasicBlock {
                    id: BasicBlockID(2),
                    instructions: vec![Instr::Unreachable],
                },
            ],
            env_ty: None,
            env_reg: None,
            size: 1,
        };

        let module = IRModule {
            functions: vec![func.clone()],
            constants: vec![],
        };
        let optimized = DeadCodeEliminator::new().run(module);
        let optimized_func = optimized
            .functions
            .iter()
            .find(|f| f.name == "@main")
            .unwrap();

        assert_eq!(optimized_func.blocks.len(), 2);
        assert!(optimized_func.blocks.iter().all(|b| b.id.0 < 2));
    }

    #[test]
    fn removes_unread_registers() {
        let func = IRFunction {
            debug_info: Default::default(),
            name: "@main".into(),
            ty: IRType::Func(vec![], IRType::Void.into()),
            blocks: vec![BasicBlock {
                id: BasicBlockID(0),
                instructions: vec![
                    Instr::ConstantInt(Register(1), 1),
                    Instr::ConstantInt(Register(2), 2),
                    Instr::ConstantInt(Register(3), 3),
                    Instr::ConstantInt(Register(4), 4),
                    Instr::Ret(IRType::Int, Some(Register(4).into())),
                ],
            }],
            env_ty: None,
            env_reg: None,
            size: 1,
        };

        let module = IRModule {
            functions: vec![func.clone()],
            constants: vec![],
        };
        let optimized = DeadCodeEliminator::new().run(module);
        let optimized_func = optimized
            .functions
            .iter()
            .find(|f| f.name == "@main")
            .unwrap();

        let block = &optimized_func.blocks[0];
        assert_eq!(
            block.instructions,
            &[
                Instr::ConstantInt(Register(4), 4),
                Instr::Ret(IRType::Int, Some(Register(4).into())),
            ]
        );
    }
}
