//! Replace enum-tag comparison chains with direct switch dispatch.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::backend::mir::{
    BlockData, BlockId, CmpKind, Constant, Function, Inst, LocalId, Operand, ScalarOp, Slot, Term,
    visit_inst,
};

use super::PassResult;

struct Comparison {
    tag: LocalId,
    value: usize,
    matched: BlockId,
    failed: BlockId,
}

struct MatchSwitch<'a> {
    blocks: &'a [BlockData],
    tag_locals: &'a FxHashSet<LocalId>,
}

impl MatchSwitch<'_> {
    fn comparison(&self, block: BlockId) -> Option<Comparison> {
        let data = self.blocks.get(block)?;
        let Term::Branch {
            cond: Operand::Local(cond),
            then_block,
            else_block,
        } = data.term.as_ref()?
        else {
            return None;
        };
        let Inst::Scalar {
            dest,
            op: ScalarOp::IntCmp(CmpKind::Eq),
            a: Operand::Local(tag),
            b: Some(Operand::Const(Constant::Int(value))),
        } = data.insts.last()?
        else {
            return None;
        };
        if dest != cond || !self.tag_locals.contains(tag) {
            return None;
        }
        Some(Comparison {
            tag: *tag,
            value: usize::try_from(*value).ok()?,
            matched: *then_block,
            failed: *else_block,
        })
    }

    /// Comparison blocks reached as the failure continuation of another
    /// comparison in the same chain. Rewriting only blocks outside this set
    /// forms one switch per chain instead of one switch for every suffix.
    fn chain_continuations(&self) -> FxHashSet<BlockId> {
        let mut continuations = FxHashSet::default();
        for block in 0..self.blocks.len() {
            let Some(comparison) = self.comparison(block) else {
                continue;
            };
            if comparison.value >= usize::from(u16::MAX) - 1 {
                continue;
            }
            let Some(failed) = self.blocks.get(comparison.failed) else {
                continue;
            };
            if !failed.params.is_empty() || failed.insts.len() != 1 {
                continue;
            }
            if self
                .comparison(comparison.failed)
                .is_some_and(|next| next.tag == comparison.tag)
            {
                continuations.insert(comparison.failed);
            }
        }
        continuations
    }

    fn replacement(&self, start: BlockId) -> Option<Term> {
        let first = self.comparison(start)?;
        let tag = first.tag;
        let mut cases: FxHashMap<usize, BlockId> = FxHashMap::default();
        let mut visited = FxHashSet::default();
        let mut current = start;

        loop {
            if !visited.insert(current) {
                break;
            }
            let block = self.blocks.get(current)?;
            if current != start && (!block.params.is_empty() || block.insts.len() != 1) {
                break;
            }
            let Some(comparison) = self.comparison(current) else {
                break;
            };
            if comparison.tag != tag || comparison.value >= usize::from(u16::MAX) - 1 {
                break;
            }
            cases.entry(comparison.value).or_insert(comparison.matched);
            current = comparison.failed;
        }

        let max = cases.keys().copied().max()?;
        let mut targets = vec![current; max + 1];
        for (value, target) in cases {
            targets[value] = target;
        }
        Some(Term::Switch {
            tag: Operand::Local(tag),
            targets,
            default: current,
        })
    }
}

pub(super) fn run(function: &mut Function) -> PassResult {
    let mut definition_counts: FxHashMap<LocalId, u32> = FxHashMap::default();
    let mut tag_locals = FxHashSet::default();
    for block in &mut function.blocks {
        for inst in &mut block.insts {
            if let Inst::GetTag { dest, .. } = inst {
                tag_locals.insert(*dest);
            }
            visit_inst(inst, &mut |slot, local| {
                if slot == Slot::Def {
                    *definition_counts.entry(*local).or_insert(0) += 1;
                }
            });
        }
    }
    tag_locals.retain(|local| definition_counts.get(local) == Some(&1));

    let matcher = MatchSwitch {
        blocks: &function.blocks,
        tag_locals: &tag_locals,
    };
    let continuations = matcher.chain_continuations();
    let replacements: Vec<Option<Term>> = (0..function.blocks.len())
        .map(|block| {
            if continuations.contains(&block) {
                None
            } else {
                matcher.replacement(block)
            }
        })
        .collect();
    let mut applied = 0;
    for (block, replacement) in function.blocks.iter_mut().zip(replacements) {
        if let Some(term) = replacement {
            block.term = Some(term);
            applied += 1;
        }
    }
    PassResult::applied(applied)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn comparison(
        tag: LocalId,
        cond: LocalId,
        value: i64,
        matched: BlockId,
        failed: BlockId,
    ) -> BlockData {
        BlockData {
            params: Vec::new(),
            insts: vec![Inst::Scalar {
                dest: cond,
                op: ScalarOp::IntCmp(CmpKind::Eq),
                a: Operand::Local(tag),
                b: Some(Operand::Const(Constant::Int(value))),
            }],
            term: Some(Term::Branch {
                cond: Operand::Local(cond),
                then_block: matched,
                else_block: failed,
            }),
        }
    }

    fn terminal() -> BlockData {
        BlockData {
            params: Vec::new(),
            insts: Vec::new(),
            term: Some(Term::Return(Operand::Const(Constant::Unit))),
        }
    }

    #[test]
    fn turns_a_tag_comparison_chain_into_dense_switch_targets() {
        let mut entry = comparison(0, 1, 0, 3, 1);
        entry.insts.insert(
            0,
            Inst::GetTag {
                dest: 0,
                src: Operand::Local(5),
            },
        );
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "match".into(),
            arity: 1,
            locals: crate::backend::mir::LocalInfo::uniform(6),
            blocks: vec![
                entry,
                comparison(0, 2, 2, 4, 2),
                terminal(),
                terminal(),
                terminal(),
            ],
        };

        assert_eq!(run(&mut function).applied, 1);
        assert!(matches!(
            &function.blocks[0].term,
            Some(Term::Switch { tag: Operand::Local(0), targets, default: 2 })
                if targets == &[3, 2, 4]
        ));
        assert!(matches!(function.blocks[1].term, Some(Term::Branch { .. })));
    }

    #[test]
    fn requires_tags_and_does_not_bypass_instructionful_continuations() {
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "not_a_match".into(),
            arity: 1,
            locals: crate::backend::mir::LocalInfo::uniform(4),
            blocks: vec![
                comparison(0, 1, 0, 2, 1),
                comparison(0, 2, 1, 2, 2),
                terminal(),
            ],
        };
        assert_eq!(run(&mut function).applied, 0);

        function.blocks[0].insts.insert(
            0,
            Inst::GetTag {
                dest: 0,
                src: Operand::Local(3),
            },
        );
        function.blocks[1].insts.insert(
            0,
            Inst::GetTag {
                dest: 3,
                src: Operand::Local(3),
            },
        );
        assert_eq!(run(&mut function).applied, 2);
        assert!(matches!(
            &function.blocks[0].term,
            Some(Term::Switch { targets, default: 1, .. }) if targets == &[2]
        ));
    }
}
