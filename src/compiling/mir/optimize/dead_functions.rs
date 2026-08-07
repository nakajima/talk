//! Remove functions unreachable from the module entry and exports.
//!
//! Inlining and call forwarding can erase a function's last incoming edge
//! after demand-driven MIR construction has already emitted it. Compacting
//! here keeps that dead code out of the finalized module all targets consume.

use crate::compiling::mir::build::{Inst, Program};

use super::PassResult;

pub(super) fn run(program: &mut Program) -> PassResult {
    let mut reachable = vec![false; program.functions.len()];
    let mut pending = Vec::with_capacity(1 + program.exports.len());
    pending.push(program.entry);
    pending.extend(program.exports.iter().map(|(_, func)| *func));

    while let Some(id) = pending.pop() {
        if reachable[id] {
            continue;
        }
        reachable[id] = true;
        for block in &program.functions[id].blocks {
            for inst in &block.insts {
                match inst {
                    Inst::Call { func, .. } | Inst::MakeClosure { func, .. }
                        if !reachable[*func] =>
                    {
                        pending.push(*func);
                    }
                    _ => {}
                }
            }
        }
    }

    let removed = reachable.iter().filter(|live| !**live).count() as u64;
    if removed == 0 {
        return PassResult::unchanged();
    }

    let mut remap = vec![usize::MAX; program.functions.len()];
    let old_functions = std::mem::take(&mut program.functions);
    program
        .functions
        .reserve(old_functions.len() - removed as usize);
    for (old_id, function) in old_functions.into_iter().enumerate() {
        if reachable[old_id] {
            remap[old_id] = program.functions.len();
            program.functions.push(function);
        }
    }

    program.entry = remap[program.entry];
    for (_, func) in &mut program.exports {
        *func = remap[*func];
    }
    for function in &mut program.functions {
        for block in &mut function.blocks {
            for inst in &mut block.insts {
                match inst {
                    Inst::Call { func, .. } | Inst::MakeClosure { func, .. } => {
                        *func = remap[*func];
                    }
                    _ => {}
                }
            }
        }
    }

    PassResult::applied(removed)
}

#[cfg(test)]
mod tests {
    use crate::compiling::mir::build::{
        BlockData, Constant, Function, Inst, LocalInfo, Operand, Program, Term,
    };

    fn function(name: &str, insts: Vec<Inst>) -> Function {
        Function {
            debug_names: None,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: name.into(),
            arity: 0,
            locals: LocalInfo::uniform(1),
            blocks: vec![BlockData {
                debug: None,
                params: Vec::new(),
                insts,
                term: Some(Term::Return(Operand::Const(Constant::Unit))),
            }],
        }
    }

    fn call(func: usize) -> Inst {
        Inst::Call {
            dest: 0,
            func,
            args: Vec::new(),
            unwind: None,
        }
    }

    fn closure(func: usize) -> Inst {
        Inst::MakeClosure {
            dest: 0,
            func,
            env: Vec::new(),
        }
    }

    fn program(functions: Vec<Function>, entry: usize, exports: Vec<(&str, usize)>) -> Program {
        Program {
            debug_files: Vec::new(),
            debug_sources: Vec::new(),
            functions,
            entry,
            global_slots: 0,
            exports: exports
                .into_iter()
                .map(|(name, func)| (name.into(), func))
                .collect(),
            layout_table: Vec::new(),
            display: Default::default(),
            string_symbol: crate::compiling::mir::build::mir_string(),
            storage_symbol: crate::compiling::mir::build::mir_storage(),
        }
    }

    #[test]
    fn removes_an_unreferenced_function() {
        let mut program = program(
            vec![function("dead", Vec::new()), function("entry", Vec::new())],
            1,
            Vec::new(),
        );

        let result = super::run(&mut program);

        assert_eq!(result.applied, 1);
        assert_eq!(program.entry, 0);
        assert_eq!(program.functions.len(), 1);
        assert_eq!(program.functions[0].name, "entry");
    }

    #[test]
    fn retains_a_transitive_direct_call_chain() {
        let mut program = program(
            vec![
                function("entry", vec![call(1)]),
                function("middle", vec![call(2)]),
                function("target", Vec::new()),
            ],
            0,
            Vec::new(),
        );

        let result = super::run(&mut program);

        assert_eq!(result.applied, 0);
        assert_eq!(program.functions.len(), 3);
    }

    #[test]
    fn retains_a_closure_body_built_by_reachable_code() {
        let mut program = program(
            vec![
                function("entry", vec![closure(1)]),
                function("closure", Vec::new()),
            ],
            0,
            Vec::new(),
        );

        let result = super::run(&mut program);

        assert_eq!(result.applied, 0);
        assert_eq!(program.functions.len(), 2);
    }

    #[test]
    fn does_not_follow_closures_built_only_by_dead_code() {
        let mut program = program(
            vec![
                function("entry", Vec::new()),
                function("dead_maker", vec![closure(2)]),
                function("dead_closure", Vec::new()),
            ],
            0,
            Vec::new(),
        );

        let result = super::run(&mut program);

        assert_eq!(result.applied, 2);
        assert_eq!(program.functions.len(), 1);
        assert_eq!(program.functions[0].name, "entry");
    }

    #[test]
    fn retains_exports_not_reachable_from_the_entry() {
        let mut program = program(
            vec![
                function("entry", Vec::new()),
                function("export", vec![call(2)]),
                function("export_target", Vec::new()),
                function("dead", Vec::new()),
            ],
            0,
            vec![("answer", 1)],
        );

        let result = super::run(&mut program);

        assert_eq!(result.applied, 1);
        assert_eq!(program.exports, vec![("answer".into(), 1)]);
        assert_eq!(program.functions.len(), 3);
    }

    #[test]
    fn compacts_in_stable_order_and_remaps_every_function_reference() {
        let mut program = program(
            vec![
                function("dead_before", Vec::new()),
                function("entry", vec![call(3), closure(5)]),
                function("dead_between", Vec::new()),
                function("called", Vec::new()),
                function("export", vec![call(3)]),
                function("closure", Vec::new()),
            ],
            1,
            vec![("run", 4)],
        );

        let result = super::run(&mut program);

        assert_eq!(result.applied, 2);
        assert_eq!(program.entry, 0);
        assert_eq!(program.exports, vec![("run".into(), 2)]);
        assert_eq!(
            program
                .functions
                .iter()
                .map(|function| function.name.as_str())
                .collect::<Vec<_>>(),
            vec!["entry", "called", "export", "closure"]
        );
        assert!(matches!(
            program.functions[0].blocks[0].insts[0],
            Inst::Call { func: 1, .. }
        ));
        assert!(matches!(
            program.functions[0].blocks[0].insts[1],
            Inst::MakeClosure { func: 3, .. }
        ));
        assert!(matches!(
            program.functions[2].blocks[0].insts[0],
            Inst::Call { func: 1, .. }
        ));
    }

    #[test]
    fn reports_no_change_for_an_already_closed_module() {
        let mut program = program(vec![function("entry", Vec::new())], 0, Vec::new());

        let result = super::run(&mut program);

        assert!(!result.changed);
        assert_eq!(result.applied, 0);
    }
}
