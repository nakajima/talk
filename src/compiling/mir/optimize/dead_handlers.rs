//! Remove handler installations for effects never requested by reachable MIR.
//!
//! This starts deliberately narrow: the clause closure must capture only the
//! continuation created for the handler. Capturing user values can involve
//! ownership preparation that is not safe to erase as an isolated instruction
//! window.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::compiling::mir::build::{
    Inst, LocalId, MirSymbol, Operand, Program, visit_inst, visit_term,
};

use super::PassResult;

pub(super) fn run(program: &mut Program) -> PassResult {
    let requested: FxHashSet<MirSymbol> = program
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .flat_map(|block| &block.insts)
        .filter_map(|inst| match inst {
            Inst::FindHandler { effect, .. } => Some(*effect),
            _ => None,
        })
        .collect();

    let mut removed = 0;
    for function in &mut program.functions {
        let mut uses: FxHashMap<LocalId, u32> = FxHashMap::default();
        for block in &mut function.blocks {
            for inst in &mut block.insts {
                visit_inst(inst, &mut |slot, local| {
                    if slot.is_use() {
                        *uses.entry(*local).or_insert(0) += 1;
                    }
                });
            }
            if let Some(term) = &mut block.term {
                visit_term(term, &mut |slot, local| {
                    if slot.is_use() {
                        *uses.entry(*local).or_insert(0) += 1;
                    }
                });
            }
        }

        for block in &mut function.blocks {
            let mut index = 0;
            while index + 2 < block.insts.len() {
                let removable = match (
                    &block.insts[index],
                    &block.insts[index + 1],
                    &block.insts[index + 2],
                ) {
                    (
                        Inst::MakeCont { dest: cont },
                        Inst::MakeClosure {
                            dest: clause, env, ..
                        },
                        Inst::PushHandler {
                            effect,
                            clause: Operand::Local(pushed_clause),
                            cont: Operand::Local(pushed_cont),
                        },
                    ) => {
                        !requested.contains(effect)
                            && *clause == *pushed_clause
                            && *cont == *pushed_cont
                            && env.as_slice() == [Operand::Local(*cont)]
                            && uses.get(cont) == Some(&2)
                            && uses.get(clause) == Some(&1)
                    }
                    _ => false,
                };
                if removable {
                    block.drain_insts(index..index + 3);
                    removed += 1;
                } else {
                    index += 1;
                }
            }
        }
    }

    PassResult::applied(removed)
}

#[cfg(test)]
mod tests {
    use crate::compiling::mir::build::{
        BlockData, Constant, Function, Inst, LocalInfo, MirSymbol, MirSymbolKind, Operand, Program,
        Term,
    };

    const EFFECT: MirSymbol = MirSymbol {
        kind: MirSymbolKind::Effect,
        module: 1,
        local: 1,
    };

    fn function(insts: Vec<Inst>) -> Function {
        Function {
            debug_names: None,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "function".into(),
            arity: 0,
            locals: LocalInfo::uniform(5),
            blocks: vec![BlockData {
                debug: None,
                params: Vec::new(),
                insts,
                term: Some(Term::Return(Operand::Const(Constant::Unit))),
            }],
        }
    }

    fn setup(effect: MirSymbol, env: Vec<Operand>) -> Vec<Inst> {
        vec![
            Inst::MakeCont { dest: 0 },
            Inst::MakeClosure {
                dest: 1,
                func: 1,
                env,
            },
            Inst::PushHandler {
                effect,
                clause: Operand::Local(1),
                cont: Operand::Local(0),
            },
        ]
    }

    fn program(functions: Vec<Function>) -> Program {
        Program {
            debug_files: Vec::new(),
            debug_sources: Vec::new(),
            functions,
            entry: 0,
            global_slots: 0,
            exports: Vec::new(),
            layout_table: Vec::new(),
            display: Default::default(),
            string_symbol: crate::compiling::mir::build::mir_string(),
            storage_symbol: crate::compiling::mir::build::mir_storage(),
        }
    }

    #[test]
    fn removes_captureless_setup_for_an_unrequested_effect() {
        let mut program = program(vec![
            function(setup(EFFECT, vec![Operand::Local(0)])),
            function(Vec::new()),
        ]);

        let result = super::run(&mut program);

        assert_eq!(result.applied, 1);
        assert!(program.functions[0].blocks[0].insts.is_empty());
    }

    #[test]
    fn keeps_setup_when_the_effect_is_requested_anywhere() {
        let mut requester = setup(EFFECT, vec![Operand::Local(0)]);
        requester.push(Inst::FindHandler {
            clause: 2,
            cont: 3,
            index: 4,
            effect: EFFECT,
        });
        let mut program = program(vec![function(requester), function(Vec::new())]);

        let result = super::run(&mut program);

        assert_eq!(result.applied, 0);
        assert_eq!(program.functions[0].blocks[0].insts.len(), 4);
    }

    #[test]
    fn keeps_setup_that_captures_a_user_value() {
        let mut program = program(vec![
            function(setup(EFFECT, vec![Operand::Local(0), Operand::Local(2)])),
            function(Vec::new()),
        ]);

        let result = super::run(&mut program);

        assert_eq!(result.applied, 0);
        assert_eq!(program.functions[0].blocks[0].insts.len(), 3);
    }

    #[test]
    fn keeps_setup_values_used_after_installation() {
        let mut insts = setup(EFFECT, vec![Operand::Local(0)]);
        insts.push(Inst::Copy {
            dest: 2,
            src: Operand::Local(1),
        });
        let mut program = program(vec![function(insts), function(Vec::new())]);

        let result = super::run(&mut program);

        assert_eq!(result.applied, 0);
        assert_eq!(program.functions[0].blocks[0].insts.len(), 4);
    }

    #[test]
    fn removes_only_effects_absent_from_the_module() {
        let requested_effect = MirSymbol { local: 2, ..EFFECT };
        let mut requested = setup(requested_effect, vec![Operand::Local(0)]);
        requested.push(Inst::FindHandler {
            clause: 2,
            cont: 3,
            index: 4,
            effect: requested_effect,
        });
        let mut program = program(vec![
            function(setup(EFFECT, vec![Operand::Local(0)])),
            function(Vec::new()),
            function(requested),
        ]);

        let result = super::run(&mut program);

        assert_eq!(result.applied, 1);
        assert!(program.functions[0].blocks[0].insts.is_empty());
        assert_eq!(program.functions[2].blocks[0].insts.len(), 4);
        let Inst::PushHandler { effect, .. } = program.functions[2].blocks[0].insts[2] else {
            panic!("requested handler setup was not retained");
        };
        assert_eq!(effect, requested_effect);
    }
}
