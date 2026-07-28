//! Remove MIR blocks that cannot be entered from the function entry.

use crate::backend::mir::{BlockData, Function, Inst, Term};

use super::PassResult;

struct Reachability {
    reachable: Vec<bool>,
}

impl Reachability {
    fn analyze(blocks: &[BlockData]) -> Self {
        let mut reachable = vec![false; blocks.len()];
        if blocks.is_empty() {
            return Self { reachable };
        }
        let mut pending = vec![0usize];
        while let Some(block) = pending.pop() {
            if reachable[block] {
                continue;
            }
            reachable[block] = true;
            for inst in &blocks[block].insts {
                match inst {
                    Inst::Call {
                        unwind: Some(target),
                        ..
                    }
                    | Inst::CallIndirect {
                        unwind: Some(target),
                        ..
                    } if !reachable[*target] => pending.push(*target),
                    _ => {}
                }
            }
            match blocks[block].term {
                Some(Term::Goto(target, _)) if !reachable[target] => pending.push(target),
                Some(Term::Branch {
                    then_block,
                    else_block,
                    ..
                }) => {
                    if !reachable[then_block] {
                        pending.push(then_block);
                    }
                    if !reachable[else_block] {
                        pending.push(else_block);
                    }
                }
                _ => {}
            }
        }
        Self { reachable }
    }

    fn compact(self, function: &mut Function) -> PassResult {
        let removed = self
            .reachable
            .iter()
            .filter(|reachable| !**reachable)
            .count() as u64;
        if removed == 0 {
            return PassResult::unchanged();
        }

        let mut remap = vec![usize::MAX; self.reachable.len()];
        let mut old = std::mem::take(&mut function.blocks)
            .into_iter()
            .map(Some)
            .collect::<Vec<_>>();
        for (old_id, reachable) in self.reachable.into_iter().enumerate() {
            if reachable {
                remap[old_id] = function.blocks.len();
                if let Some(block) = old[old_id].take() {
                    function.blocks.push(block);
                }
            }
        }

        for block in &mut function.blocks {
            for inst in &mut block.insts {
                match inst {
                    Inst::Call {
                        unwind: Some(target),
                        ..
                    }
                    | Inst::CallIndirect {
                        unwind: Some(target),
                        ..
                    } => *target = remap[*target],
                    _ => {}
                }
            }
            match &mut block.term {
                Some(Term::Goto(target, _)) => *target = remap[*target],
                Some(Term::Branch {
                    then_block,
                    else_block,
                    ..
                }) => {
                    *then_block = remap[*then_block];
                    *else_block = remap[*else_block];
                }
                _ => {}
            }
        }
        PassResult::applied(removed)
    }
}

pub(super) fn run(function: &mut Function) -> PassResult {
    Reachability::analyze(&function.blocks).compact(function)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::mir::{Constant, Operand};

    #[test]
    fn removes_dead_blocks_and_remaps_targets() {
        let mut function = Function {
            name: "reachable".into(),
            arity: 0,
            n_locals: 1,
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Goto(2, Vec::new())),
                },
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Trap("dead")),
                },
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Return(Operand::Const(Constant::Unit))),
                },
            ],
        };

        assert_eq!(run(&mut function).applied, 1);
        assert_eq!(function.blocks.len(), 2);
        assert!(matches!(function.blocks[0].term, Some(Term::Goto(1, _))));
    }
}
