//! The shared control-flow graph used by MIR dataflow analyses.
//!
//! The graph includes both terminator and unwind edges. Analyses own their
//! lattice and transfer semantics, but topology and fixpoint traversal live
//! here so ownership, liveness, escape checking, verification, and register
//! allocation cannot disagree about reachability.

use talk_mir::{BlockData, BlockId, Inst, Term};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EdgePosition {
    Unwind(u32),
    Terminator(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Predecessor {
    pub block: BlockId,
    pub position: EdgePosition,
}

pub(crate) trait Forward {
    type State: Clone;

    fn join(&mut self, target: BlockId, existing: &mut Self::State, incoming: &Self::State)
    -> bool;

    fn transfer(&mut self, block: BlockId, state: Self::State) -> Vec<(BlockId, Self::State)>;
}

pub(crate) struct Cfg {
    pub successors: Vec<Vec<BlockId>>,
    pub predecessors: Vec<Vec<Predecessor>>,
}

impl Cfg {
    pub fn new(blocks: &[BlockData]) -> Self {
        let mut successors = vec![Vec::new(); blocks.len()];
        let mut predecessors = vec![Vec::new(); blocks.len()];
        for (block, data) in blocks.iter().enumerate() {
            successors[block] = Self::block_successors(data);
            for (index, inst) in data.insts.iter().enumerate() {
                if let Some(target) = Self::unwind_target(inst) {
                    predecessors[target].push(Predecessor {
                        block,
                        position: EdgePosition::Unwind(index as u32),
                    });
                }
            }
            for (position, target) in Self::term_successors(data.term.as_ref())
                .into_iter()
                .enumerate()
            {
                predecessors[target].push(Predecessor {
                    block,
                    position: EdgePosition::Terminator(position),
                });
            }
        }
        Self {
            successors,
            predecessors,
        }
    }

    pub fn forward<A: Forward>(&self, analysis: &mut A, entry: A::State) -> Vec<Option<A::State>> {
        let mut entries = vec![None; self.successors.len()];
        if entries.is_empty() {
            return entries;
        }
        entries[0] = Some(entry);
        let mut worklist = vec![0];
        while let Some(block) = worklist.pop() {
            let Some(state) = entries[block].clone() else {
                continue;
            };
            for (target, incoming) in analysis.transfer(block, state) {
                match &mut entries[target] {
                    None => {
                        entries[target] = Some(incoming);
                        worklist.push(target);
                    }
                    Some(existing) => {
                        if analysis.join(target, existing, &incoming) {
                            worklist.push(target);
                        }
                    }
                }
            }
        }
        entries
    }

    pub fn backward_bits(
        &self,
        words: usize,
        mut transfer: impl FnMut(BlockId, &mut Vec<u64>),
    ) -> Vec<Vec<u64>> {
        let mut entries = vec![vec![0; words]; self.successors.len()];
        let mut state = vec![0; words];
        let mut changed = true;
        while changed {
            changed = false;
            for block in (0..self.successors.len()).rev() {
                state.fill(0);
                for target in &self.successors[block] {
                    bits::union(&mut state, &entries[*target]);
                }
                transfer(block, &mut state);
                if state != entries[block] {
                    std::mem::swap(&mut entries[block], &mut state);
                    changed = true;
                }
            }
        }
        entries
    }

    pub fn block_successors(block: &BlockData) -> Vec<BlockId> {
        let mut successors: Vec<BlockId> =
            block.insts.iter().filter_map(Self::unwind_target).collect();
        successors.extend(Self::term_successors(block.term.as_ref()));
        successors
    }

    pub fn term_successors(term: Option<&Term>) -> Vec<BlockId> {
        match term {
            Some(Term::Goto(target, _)) => vec![*target],
            Some(Term::Branch {
                then_block,
                else_block,
                ..
            }) => vec![*then_block, *else_block],
            Some(Term::Switch {
                targets, default, ..
            }) => targets
                .iter()
                .copied()
                .chain(std::iter::once(*default))
                .collect(),
            Some(Term::Return(_) | Term::Trap(_) | Term::UnwindRet) | None => Vec::new(),
        }
    }

    pub fn unwind_target(inst: &Inst) -> Option<BlockId> {
        match inst {
            Inst::Call {
                unwind: Some(target),
                ..
            }
            | Inst::CallIndirect {
                unwind: Some(target),
                ..
            }
            | Inst::Suspend {
                unwind: Some(target),
                ..
            } => Some(*target),
            _ => None,
        }
    }
}

pub(crate) mod bits {
    use talk_mir::LocalId;

    pub fn set(bits: &mut [u64], local: LocalId) {
        bits[usize::from(local) / 64] |= 1u64 << (usize::from(local) % 64);
    }

    pub fn clear(bits: &mut [u64], local: LocalId) {
        bits[usize::from(local) / 64] &= !(1u64 << (usize::from(local) % 64));
    }

    pub fn get(bits: &[u64], local: LocalId) -> bool {
        bits[usize::from(local) / 64] & (1u64 << (usize::from(local) % 64)) != 0
    }

    pub fn union(dest: &mut [u64], src: &[u64]) {
        for (dest, src) in dest.iter_mut().zip(src) {
            *dest |= *src;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use talk_mir::{Constant, Operand};

    fn block(insts: Vec<Inst>, term: Term) -> BlockData {
        BlockData {
            debug: None,
            params: Vec::new(),
            insts,
            term: Some(term),
        }
    }

    #[test]
    fn topology_includes_unwind_and_predecessor_positions() {
        let blocks = vec![
            block(
                vec![Inst::Call {
                    dest: 0,
                    func: 0,
                    args: Vec::new(),
                    unwind: Some(3),
                }],
                Term::Branch {
                    cond: Operand::Const(Constant::Bool(true)),
                    then_block: 1,
                    else_block: 2,
                },
            ),
            block(Vec::new(), Term::Goto(2, Vec::new())),
            block(Vec::new(), Term::Return(Operand::Const(Constant::Unit))),
            block(Vec::new(), Term::UnwindRet),
        ];
        let cfg = Cfg::new(&blocks);
        assert_eq!(cfg.successors[0], vec![3, 1, 2]);
        assert_eq!(
            cfg.predecessors[3],
            vec![Predecessor {
                block: 0,
                position: EdgePosition::Unwind(0),
            }]
        );
        assert_eq!(
            cfg.predecessors[2],
            vec![
                Predecessor {
                    block: 0,
                    position: EdgePosition::Terminator(1),
                },
                Predecessor {
                    block: 1,
                    position: EdgePosition::Terminator(0),
                },
            ]
        );
    }

    #[test]
    fn backward_bits_unions_successor_entries() {
        let blocks = vec![
            block(
                Vec::new(),
                Term::Branch {
                    cond: Operand::Const(Constant::Bool(true)),
                    then_block: 1,
                    else_block: 2,
                },
            ),
            block(Vec::new(), Term::Return(Operand::Const(Constant::Unit))),
            block(Vec::new(), Term::Return(Operand::Const(Constant::Unit))),
        ];
        let cfg = Cfg::new(&blocks);
        let entries = cfg.backward_bits(1, |block, live| match block {
            1 => bits::set(live, 1),
            2 => bits::set(live, 2),
            _ => {}
        });
        assert_eq!(entries[0], vec![0b110]);
    }
}
