//! Thread direct calls through semantically transparent forwarding functions.
//!
//! A function whose whole body is `return target(param0, ..., paramN)` adds a
//! frame without adding behavior. Direct callers can call `target` instead,
//! retaining their own destination and unwind edge. Closure construction is
//! deliberately untouched: this pass only simplifies statically named calls.

use crate::backend::mir::{FuncId, Function, Inst, Operand, Program, Term};

use super::PassResult;

struct ForwardingCalls {
    targets: Vec<Option<FuncId>>,
}

impl ForwardingCalls {
    fn for_program(program: &Program) -> Self {
        let targets = program
            .functions
            .iter()
            .map(|function| Self::target(function, program))
            .collect();
        Self { targets }
    }

    fn target(function: &Function, program: &Program) -> Option<FuncId> {
        let [block] = function.blocks.as_slice() else {
            return None;
        };
        if !block.params.is_empty() {
            return None;
        }
        let [
            Inst::Call {
                dest,
                func,
                args,
                unwind: None,
            },
        ] = block.insts.as_slice()
        else {
            return None;
        };
        let Some(Term::Return(Operand::Local(returned))) = &block.term else {
            return None;
        };
        if dest != returned
            || args.len() != usize::from(function.arity)
            || args
                .iter()
                .zip(0..function.arity)
                .any(|(arg, index)| *arg != Operand::Local(index))
            || program.functions.get(*func)?.arity != function.arity
        {
            return None;
        }
        Some(*func)
    }

    fn resolved_target(&self, original: FuncId) -> FuncId {
        let mut target = original;
        for _ in 0..self.targets.len() {
            let Some(next) = self.targets.get(target).copied().flatten() else {
                return target;
            };
            target = next;
        }
        // A forwarding cycle has no concrete implementation to call.
        original
    }

    fn apply(&self, program: &mut Program) -> PassResult {
        let mut applied = 0;
        for function in &mut program.functions {
            for block in &mut function.blocks {
                for inst in &mut block.insts {
                    let Inst::Call { func, .. } = inst else {
                        continue;
                    };
                    let target = self.resolved_target(*func);
                    if target != *func {
                        *func = target;
                        applied += 1;
                    }
                }
            }
        }
        PassResult::applied(applied)
    }
}

pub(super) fn run(program: &mut Program) -> PassResult {
    ForwardingCalls::for_program(program).apply(program)
}

#[cfg(test)]
mod tests {
    use crate::backend::mir::{BlockData, Function, Inst, Operand, Program, Term};

    fn function(arity: u16, insts: Vec<Inst>, term: Term) -> Function {
        Function {
            name: String::new(),
            arity,
            n_locals: arity + 1,
            blocks: vec![BlockData {
                params: Vec::new(),
                insts,
                term: Some(term),
            }],
        }
    }

    fn call(dest: u16, func: usize, args: Vec<Operand>, unwind: Option<usize>) -> Inst {
        Inst::Call {
            dest,
            func,
            args,
            unwind,
        }
    }

    fn program(functions: Vec<Function>) -> Program {
        Program {
            functions,
            entry: 0,
            global_slots: 0,
            exports: Vec::new(),
        }
    }

    #[test]
    fn threads_identity_forwarder_and_preserves_caller_unwind() {
        let caller = Function {
            name: String::new(),
            arity: 2,
            n_locals: 3,
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: vec![call(
                        2,
                        1,
                        vec![Operand::Local(0), Operand::Local(1)],
                        Some(1),
                    )],
                    term: Some(Term::Return(Operand::Local(2))),
                },
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::UnwindRet),
                },
            ],
        };
        let forwarder = function(
            2,
            vec![call(2, 2, vec![Operand::Local(0), Operand::Local(1)], None)],
            Term::Return(Operand::Local(2)),
        );
        let target = function(2, Vec::new(), Term::Return(Operand::Local(0)));
        let mut program = program(vec![caller, forwarder, target]);

        let result = super::run(&mut program);

        assert_eq!(result.applied, 1);
        assert!(matches!(
            program.functions[0].blocks[0].insts[0],
            Inst::Call {
                func: 2,
                unwind: Some(1),
                ..
            }
        ));
    }

    #[test]
    fn rejects_reordered_arguments_and_forwarder_unwind() {
        let target = function(2, Vec::new(), Term::Return(Operand::Local(0)));
        let reordered = function(
            2,
            vec![call(2, 0, vec![Operand::Local(1), Operand::Local(0)], None)],
            Term::Return(Operand::Local(2)),
        );
        let unwinding = function(
            2,
            vec![call(
                2,
                0,
                vec![Operand::Local(0), Operand::Local(1)],
                Some(0),
            )],
            Term::Return(Operand::Local(2)),
        );
        let caller = function(
            2,
            vec![
                call(2, 1, vec![Operand::Local(0), Operand::Local(1)], None),
                call(2, 2, vec![Operand::Local(0), Operand::Local(1)], None),
            ],
            Term::Return(Operand::Local(2)),
        );
        let mut program = program(vec![target, reordered, unwinding, caller]);

        let result = super::run(&mut program);

        assert_eq!(result.applied, 0);
        assert!(matches!(
            program.functions[3].blocks[0].insts[0],
            Inst::Call { func: 1, .. }
        ));
        assert!(matches!(
            program.functions[3].blocks[0].insts[1],
            Inst::Call { func: 2, .. }
        ));
    }
}
