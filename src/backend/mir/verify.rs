//! The ownership-balance verifier: the checker behind the trust chain
//! that the previous system's soundness review found missing (ADR 0017
//! stage 2; docs/ownership-soundness-plan.md) and the rethink's wave B
//! delivers (docs/ownership-rethink-plan.md).
//!
//! While building a function, the builder logs one event at every point
//! it decides ownership: Def when a local becomes a tracked owned value,
//! Use when one is read, Move when ownership transfers out, Drop when a
//! release is emitted. This module replays the log as a forward dataflow
//! fixpoint over the built control-flow graph (Kildall, "A Unified
//! Approach to Global Program Optimization", POPL 1973) and checks the
//! invariant the hand-threaded state can only promise: **every tracked
//! value is released exactly once on every finite path.** Concretely:
//!
//! - Drop or Move of a value not currently owned is a double release.
//! - Use of a value not currently owned is a use after move (or before
//!   initialization).
//! - A join whose predecessors disagree about a value's state breaks the
//!   path-independence `merge_arms` establishes and the unwind cleanup
//!   chains rely on.
//! - Reaching Return or UnwindRet with a value still owned is a leak.
//!
//! Unwind edges count: a call carrying an unwind target propagates the
//! state at the call into the cleanup chain, so a chain reused across
//! call sites with different live sets is caught here.
//!
//! Scope: the verifier checks the builder's decisions for consistency,
//! not for classification — a value consistently mistaken for owned
//! (bound from a borrowed payload, say) balances its own books. Deriving
//! classification from one place is drop elaboration's job (wave C).
//! Trap-terminated paths are exempt from the leak check: a trap aborts
//! the program, not the frame.

use super::{BlockData, BlockId, Inst, LocalId, Term};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FlowEvent {
    /// The local now holds a tracked owned value.
    Def(LocalId),
    /// The local's value is read (must be owned here).
    Use(LocalId),
    /// Ownership transferred out (a consume, donation, or capture).
    Move(LocalId),
    /// A release was emitted for the local's value.
    Drop(LocalId),
}

#[derive(Clone, Copy, Debug)]
pub(super) struct FlowRecord {
    pub block: BlockId,
    /// Instruction index within the block at the moment of the decision:
    /// the event happens before the instruction at this index executes.
    pub index: u32,
    pub event: FlowEvent,
}

/// Per-local state at a program point. `CONFLICT` is sticky: a join
/// disagreement is reported once and then stops propagating errors.
pub(super) const ABSENT: u8 = 0;
pub(super) const OWNED: u8 = 1;
pub(super) const DEAD: u8 = 2;
pub(super) const CONFLICT: u8 = 3;

fn state_name(state: u8) -> &'static str {
    match state {
        ABSENT => "uninitialized",
        OWNED => "owned",
        DEAD => "released",
        _ => "conflicted",
    }
}

/// Per-block-entry ownership states from the same forward fixpoint the
/// checker runs: the release planner reads these to know what is owned
/// where (drop elaboration builds on the balance model it verifies).
pub(super) fn entry_states(blocks: &[BlockData], records: &[FlowRecord]) -> Vec<Option<Vec<u8>>> {
    let mut errors = Vec::new();
    run(blocks, records, "plan", &mut errors)
}

/// Replay `records` over `blocks`; return every broken invariant.
/// `name` labels reports. An empty result is the balance proof the
/// emitted drops previously took on trust. Debug builds only: the
/// release pipeline keeps the planner (`entry_states`) and drops the
/// replay.
#[cfg(debug_assertions)]
pub(super) fn check(blocks: &[BlockData], records: &[FlowRecord], name: &str) -> Vec<String> {
    let mut errors = Vec::new();
    run(blocks, records, name, &mut errors);
    errors
}

fn run(
    blocks: &[BlockData],
    records: &[FlowRecord],
    name: &str,
    errors: &mut Vec<String>,
) -> Vec<Option<Vec<u8>>> {
    let n_locals = records
        .iter()
        .map(|record| {
            let (FlowEvent::Def(l) | FlowEvent::Use(l) | FlowEvent::Move(l) | FlowEvent::Drop(l)) =
                record.event;
            l as usize + 1
        })
        .max()
        .unwrap_or(0);
    if n_locals == 0 {
        return vec![None; blocks.len()];
    }

    let mut events: Vec<Vec<(u32, FlowEvent)>> = vec![Vec::new(); blocks.len()];
    for record in records {
        events[record.block].push((record.index, record.event));
    }
    for bucket in &mut events {
        bucket.sort_by_key(|(index, _)| *index);
    }

    let mut in_states: Vec<Option<Vec<u8>>> = vec![None; blocks.len()];
    in_states[0] = Some(vec![ABSENT; n_locals]);
    let mut worklist: Vec<BlockId> = vec![0];
    let mut reported_joins: Vec<bool> = vec![false; blocks.len()];

    while let Some(block) = worklist.pop() {
        let Some(mut state) = in_states[block].clone() else {
            continue;
        };
        let data = &blocks[block];
        let mut cursor = 0usize;
        let bucket = &events[block];

        let mut apply_until = |limit: u32, state: &mut Vec<u8>, errors: &mut Vec<String>| {
            while cursor < bucket.len() && bucket[cursor].0 <= limit {
                let (index, event) = bucket[cursor];
                cursor += 1;
                apply(event, state, block, index, name, errors);
            }
        };

        for (i, inst) in data.insts.iter().enumerate() {
            apply_until(i as u32, &mut state, errors);
            let unwind = match inst {
                Inst::Call { unwind, .. } | Inst::CallIndirect { unwind, .. } => *unwind,
                _ => None,
            };
            if let Some(target) = unwind {
                join_into(
                    target,
                    &state,
                    &mut in_states,
                    &mut worklist,
                    &mut reported_joins,
                    errors,
                    name,
                );
            }
        }
        apply_until(u32::MAX, &mut state, errors);

        match &data.term {
            Some(Term::Goto(target, _)) => join_into(
                *target,
                &state,
                &mut in_states,
                &mut worklist,
                &mut reported_joins,
                errors,
                name,
            ),
            Some(Term::Branch {
                then_block,
                else_block,
                ..
            }) => {
                for target in [*then_block, *else_block] {
                    join_into(
                        target,
                        &state,
                        &mut in_states,
                        &mut worklist,
                        &mut reported_joins,
                        errors,
                        name,
                    );
                }
            }
            Some(Term::Return(_)) | Some(Term::UnwindRet) => {
                for (local, &s) in state.iter().enumerate() {
                    if s == OWNED {
                        errors.push(format!(
                            "{name}: local {local} still owned at frame exit in block {block} (leak)"
                        ));
                    }
                }
            }
            Some(Term::Trap(_)) => {}
            None => {}
        }
    }
    in_states
}

fn apply(
    event: FlowEvent,
    state: &mut [u8],
    block: BlockId,
    index: u32,
    name: &str,
    errors: &mut Vec<String>,
) {
    match event {
        FlowEvent::Def(local) => {
            if state[local as usize] == OWNED {
                errors.push(format!(
                    "{name}: local {local} redefined while still owned at block {block} inst {index} (leak)"
                ));
            }
            state[local as usize] = OWNED;
        }
        FlowEvent::Use(local) => {
            if state[local as usize] != OWNED && state[local as usize] != CONFLICT {
                errors.push(format!(
                    "{name}: local {local} used while {} at block {block} inst {index}",
                    state_name(state[local as usize])
                ));
            }
        }
        FlowEvent::Move(local) | FlowEvent::Drop(local) => {
            let verb = if matches!(event, FlowEvent::Move(_)) {
                "moved"
            } else {
                "dropped"
            };
            match state[local as usize] {
                OWNED => state[local as usize] = DEAD,
                CONFLICT => {}
                other => {
                    errors.push(format!(
                        "{name}: local {local} {verb} while {} at block {block} inst {index} (double release)",
                        state_name(other)
                    ));
                    state[local as usize] = DEAD;
                }
            }
        }
    }
}

fn join_into(
    target: BlockId,
    incoming: &[u8],
    in_states: &mut [Option<Vec<u8>>],
    worklist: &mut Vec<BlockId>,
    reported_joins: &mut [bool],
    errors: &mut Vec<String>,
    name: &str,
) {
    match &mut in_states[target] {
        None => {
            in_states[target] = Some(incoming.to_vec());
            worklist.push(target);
        }
        Some(existing) => {
            let mut changed = false;
            for (local, (have, new)) in existing.iter_mut().zip(incoming).enumerate() {
                if *have == *new || *have == CONFLICT {
                    continue;
                }
                // Absent and Dead agree: both mean "nothing owned here"
                // (an arm-local value born and released inside one arm).
                // Only an Owned/not-Owned disagreement breaks the
                // exactly-once invariant.
                if *have != OWNED && *new != OWNED {
                    if *have != DEAD {
                        *have = DEAD;
                        changed = true;
                    }
                    continue;
                }
                if !reported_joins[target] {
                    reported_joins[target] = true;
                    errors.push(format!(
                        "{name}: block {target} joined with local {local} {} on one path and {} on another",
                        state_name(*have),
                        state_name(*new)
                    ));
                }
                *have = CONFLICT;
                changed = true;
            }
            if changed {
                worklist.push(target);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Constant, Operand};
    use super::*;

    fn block(insts: usize, term: Term) -> BlockData {
        BlockData {
            params: Vec::new(),
            insts: vec![
                Inst::Copy {
                    dest: 0,
                    src: Operand::Const(Constant::Unit),
                };
                insts
            ],
            term: Some(term),
        }
    }

    fn record(block: BlockId, index: u32, event: FlowEvent) -> FlowRecord {
        FlowRecord {
            block,
            index,
            event,
        }
    }

    #[test]
    fn balanced_straight_line_is_clean() {
        let blocks = vec![block(2, Term::Return(Operand::Const(Constant::Unit)))];
        let records = vec![
            record(0, 1, FlowEvent::Def(3)),
            record(0, 1, FlowEvent::Use(3)),
            record(0, 2, FlowEvent::Drop(3)),
        ];
        assert_eq!(check(&blocks, &records, "t"), Vec::<String>::new());
    }

    #[test]
    fn missing_release_is_a_leak() {
        let blocks = vec![block(1, Term::Return(Operand::Const(Constant::Unit)))];
        let records = vec![record(0, 0, FlowEvent::Def(2))];
        let errors = check(&blocks, &records, "t");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("leak"), "{errors:?}");
    }

    #[test]
    fn double_release_is_reported() {
        let blocks = vec![block(2, Term::Return(Operand::Const(Constant::Unit)))];
        let records = vec![
            record(0, 0, FlowEvent::Def(1)),
            record(0, 1, FlowEvent::Move(1)),
            record(0, 2, FlowEvent::Drop(1)),
        ];
        let errors = check(&blocks, &records, "t");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("double release"), "{errors:?}");
    }

    #[test]
    fn use_after_move_is_reported() {
        let blocks = vec![block(2, Term::Return(Operand::Const(Constant::Unit)))];
        let records = vec![
            record(0, 0, FlowEvent::Def(1)),
            record(0, 1, FlowEvent::Move(1)),
            record(0, 2, FlowEvent::Use(1)),
        ];
        let errors = check(&blocks, &records, "t");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("used while released"), "{errors:?}");
    }

    #[test]
    fn divergent_join_is_reported_once() {
        // block 0 branches to 1 and 2; only block 1 drops; both goto 3.
        let blocks = vec![
            block(
                1,
                Term::Branch {
                    cond: Operand::Local(9),
                    then_block: 1,
                    else_block: 2,
                },
            ),
            block(1, Term::Goto(3, Vec::new())),
            block(0, Term::Goto(3, Vec::new())),
            block(0, Term::Return(Operand::Const(Constant::Unit))),
        ];
        let records = vec![
            record(0, 0, FlowEvent::Def(1)),
            record(1, 0, FlowEvent::Drop(1)),
        ];
        let errors = check(&blocks, &records, "t");
        assert!(
            errors.iter().any(|error| error.contains("joined with")),
            "{errors:?}"
        );
        assert_eq!(
            errors
                .iter()
                .filter(|error| error.contains("joined with"))
                .count(),
            1,
            "one report per join: {errors:?}"
        );
    }

    #[test]
    fn balanced_branches_are_clean() {
        let blocks = vec![
            block(
                1,
                Term::Branch {
                    cond: Operand::Local(9),
                    then_block: 1,
                    else_block: 2,
                },
            ),
            block(1, Term::Goto(3, Vec::new())),
            block(1, Term::Goto(3, Vec::new())),
            block(0, Term::Return(Operand::Const(Constant::Unit))),
        ];
        let records = vec![
            record(0, 0, FlowEvent::Def(1)),
            record(1, 0, FlowEvent::Drop(1)),
            record(2, 0, FlowEvent::Move(1)),
        ];
        assert_eq!(check(&blocks, &records, "t"), Vec::<String>::new());
    }

    #[test]
    fn unwind_edge_carries_state_into_the_cleanup_chain() {
        // A call in block 0 unwinds to block 1, which must drop the one
        // live value and UnwindRet. A second live value the chain misses
        // is a leak at UnwindRet.
        let blocks = vec![
            BlockData {
                params: Vec::new(),
                insts: vec![Inst::Call {
                    dest: 7,
                    func: 0,
                    args: Vec::new(),
                    unwind: Some(1),
                }],
                term: Some(Term::Return(Operand::Const(Constant::Unit))),
            },
            block(1, Term::UnwindRet),
        ];
        let clean = vec![
            record(0, 0, FlowEvent::Def(1)),
            record(1, 0, FlowEvent::Drop(1)),
            // The normal path releases it too (after the call).
            record(0, 1, FlowEvent::Drop(1)),
        ];
        assert_eq!(check(&blocks, &clean, "t"), Vec::<String>::new());

        let leaky = vec![
            record(0, 0, FlowEvent::Def(1)),
            record(0, 0, FlowEvent::Def(2)),
            record(1, 0, FlowEvent::Drop(1)),
            record(0, 1, FlowEvent::Drop(1)),
            record(0, 1, FlowEvent::Drop(2)),
        ];
        let errors = check(&blocks, &leaky, "t");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("leak") && errors[0].contains("block 1"),
            "{errors:?}"
        );
    }

    #[test]
    fn loop_back_edge_agreement_is_checked() {
        // block 0 defs and enters loop head 1; body 2 drops and redefines
        // per iteration, so the back edge agrees with entry; exit 3 drops.
        let blocks = vec![
            block(1, Term::Goto(1, Vec::new())),
            block(
                0,
                Term::Branch {
                    cond: Operand::Local(9),
                    then_block: 2,
                    else_block: 3,
                },
            ),
            block(2, Term::Goto(1, Vec::new())),
            block(1, Term::Return(Operand::Const(Constant::Unit))),
        ];
        let records = vec![
            record(0, 0, FlowEvent::Def(1)),
            record(2, 0, FlowEvent::Drop(1)),
            record(2, 1, FlowEvent::Def(1)),
            record(3, 0, FlowEvent::Drop(1)),
        ];
        assert_eq!(check(&blocks, &records, "t"), Vec::<String>::new());
    }
}
