//! Remove unused MIR computations that are known to be total and effect free.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::backend::mir::{Function, Inst, LocalId, ScalarOp, visit_inst, visit_term};

use super::PassResult;

struct UseCounts {
    counts: FxHashMap<LocalId, u32>,
    block_params: FxHashSet<LocalId>,
}

impl UseCounts {
    fn collect(function: &mut Function) -> Self {
        let mut counts = FxHashMap::default();
        let mut block_params = FxHashSet::default();
        for block in &mut function.blocks {
            block_params.extend(block.params.iter().copied());
            for inst in &mut block.insts {
                visit_inst(inst, &mut |slot, local| {
                    if slot.is_use() {
                        *counts.entry(*local).or_insert(0) += 1;
                    }
                });
            }
            if let Some(term) = &mut block.term {
                visit_term(term, &mut |slot, local| {
                    if slot.is_use() {
                        *counts.entry(*local).or_insert(0) += 1;
                    }
                });
            }
        }
        Self {
            counts,
            block_params,
        }
    }

    fn unused(&self, local: LocalId, arity: u16) -> bool {
        local >= arity
            && !self.block_params.contains(&local)
            && self.counts.get(&local).copied().unwrap_or(0) == 0
    }
}

fn removable(inst: &Inst) -> Option<LocalId> {
    match inst {
        Inst::Copy { dest, .. } => Some(*dest),
        // A member read is total and effect-free: offsets are resolved
        // against the published layout, and retains are separate
        // instructions. Chain folding (ADR 0046) bypasses intermediate
        // reads and relies on this pass to collect them.
        Inst::Field { dest, .. } => Some(*dest),
        Inst::Scalar { dest, op, .. } if !matches!(op, ScalarOp::IntDiv | ScalarOp::IntToByte) => {
            Some(*dest)
        }
        _ => None,
    }
}

pub(super) fn run(function: &mut Function) -> PassResult {
    let mut applied = 0;
    loop {
        let uses = UseCounts::collect(function);
        let mut removed = 0;
        for block in &mut function.blocks {
            block.insts.retain(|inst| {
                let remove = removable(inst).is_some_and(|dest| uses.unused(dest, function.arity));
                if remove {
                    removed += 1;
                }
                !remove
            });
        }
        if removed == 0 {
            return PassResult::applied(applied);
        }
        applied += removed;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::mir::{BlockData, Constant, Operand, ScalarOp, Term};

    #[test]
    fn removes_dead_pure_chains() {
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "dead".into(),
            arity: 0,
            locals: crate::backend::mir::LocalInfo::uniform(2),
            blocks: vec![BlockData {
                params: Vec::new(),
                insts: vec![
                    Inst::Copy {
                        dest: 0,
                        src: Operand::Const(Constant::Int(1)),
                    },
                    Inst::Scalar {
                        dest: 1,
                        op: ScalarOp::IntAdd,
                        a: Operand::Local(0),
                        b: Some(Operand::Const(Constant::Int(2))),
                    },
                ],
                term: Some(Term::Return(Operand::Const(Constant::Unit))),
            }],
        };

        assert_eq!(run(&mut function).applied, 2);
        assert!(function.blocks[0].insts.is_empty());
    }

    #[test]
    fn removes_dead_member_reads() {
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "dead_read".into(),
            arity: 1,
            locals: crate::backend::mir::LocalInfo::uniform(2),
            blocks: vec![BlockData {
                params: Vec::new(),
                insts: vec![Inst::Field {
                    dest: 1,
                    src: Operand::Local(0),
                    container: 0,
                    offset: 0,
                    member: None,
                }],
                term: Some(Term::Return(Operand::Const(Constant::Unit))),
            }],
        };

        assert_eq!(run(&mut function).applied, 1);
        assert!(function.blocks[0].insts.is_empty());
    }

    #[test]
    fn keeps_unused_operations_that_can_trap() {
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "trap".into(),
            arity: 0,
            locals: crate::backend::mir::LocalInfo::uniform(1),
            blocks: vec![BlockData {
                params: Vec::new(),
                insts: vec![Inst::Scalar {
                    dest: 0,
                    op: ScalarOp::IntDiv,
                    a: Operand::Const(Constant::Int(1)),
                    b: Some(Operand::Const(Constant::Int(0))),
                }],
                term: Some(Term::Return(Operand::Const(Constant::Unit))),
            }],
        };

        assert_eq!(run(&mut function).applied, 0);
        assert_eq!(function.blocks[0].insts.len(), 1);
    }
}
