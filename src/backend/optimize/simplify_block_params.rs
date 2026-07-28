//! Remove unused block parameters and their incoming edge arguments.

use rustc_hash::FxHashSet;

use crate::backend::mir::{Function, LocalId, Slot, Term, visit_inst, visit_term};

use super::PassResult;

struct UsedLocals {
    locals: FxHashSet<LocalId>,
}

impl UsedLocals {
    fn collect(function: &mut Function) -> Self {
        let mut locals = FxHashSet::default();
        for block in &mut function.blocks {
            for inst in &mut block.insts {
                visit_inst(inst, &mut |slot, local| {
                    if slot == Slot::Use {
                        locals.insert(*local);
                    }
                });
            }
            if let Some(term) = &mut block.term {
                visit_term(term, &mut |slot, local| {
                    if slot == Slot::Use {
                        locals.insert(*local);
                    }
                });
            }
        }
        Self { locals }
    }
}

pub(super) fn run(function: &mut Function) -> PassResult {
    let used = UsedLocals::collect(function);
    let removals = function
        .blocks
        .iter()
        .map(|block| {
            block
                .params
                .iter()
                .enumerate()
                .filter_map(|(index, param)| (!used.locals.contains(param)).then_some(index))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let applied = removals.iter().map(Vec::len).sum::<usize>() as u64;
    if applied == 0 {
        return PassResult::unchanged();
    }

    for (block, removed) in function.blocks.iter_mut().zip(&removals) {
        for &index in removed.iter().rev() {
            block.params.remove(index);
        }
    }
    for block in &mut function.blocks {
        let Some(Term::Goto(target, args)) = &mut block.term else {
            continue;
        };
        for &index in removals[*target].iter().rev() {
            debug_assert!(
                index < args.len(),
                "MIR edge argument count must match block parameters"
            );
            if index < args.len() {
                args.remove(index);
            }
        }
    }
    PassResult::applied(applied)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::mir::{BlockData, Constant, Operand};

    #[test]
    fn removes_unused_parameter_and_matching_edge_argument() {
        let mut function = Function {
            name: "params".into(),
            arity: 0,
            n_locals: 3,
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Goto(
                        1,
                        vec![
                            Operand::Const(Constant::Int(1)),
                            Operand::Const(Constant::Int(2)),
                        ],
                    )),
                },
                BlockData {
                    params: vec![1, 2],
                    insts: Vec::new(),
                    term: Some(Term::Return(Operand::Local(1))),
                },
            ],
        };

        assert_eq!(run(&mut function).applied, 1);
        assert_eq!(function.blocks[1].params, vec![1]);
        assert!(matches!(
            function.blocks[0].term,
            Some(Term::Goto(1, ref args)) if args == &[Operand::Const(Constant::Int(1))]
        ));
    }
}
