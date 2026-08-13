//! Computed flow checks over the built CFG (ADR 0057 slice 4;
//! docs/ownership.md's "compute it, don't thread it"). The checking
//! rules here used to be hand-threaded through `FunctionBuilder` — a
//! taint set for frame-anchored closures hooked into every `push` and
//! `terminate`, and a moved-globals set saved, restored, and unioned by
//! hand at every `if`/`loop`/`match` join. Both replay here as forward
//! fixpoints over the finished blocks: lowering records only the seeds
//! and the type-dependent sinks it alone can classify; propagation and
//! joins come from the control-flow graph itself, so a new construct
//! cannot forget a merge.

use rustc_hash::FxHashSet;

use super::verify::{FlowEvent, FlowRecord};
use super::{BackendError, BlockData, BlockId, Inst, LocalId, Operand, Term, anchored_escape};
use crate::span::Span;

/// Every violation the recorded events and the CFG prove, in block/
/// instruction order (deterministic across runs).
pub(super) fn check(
    blocks: &[BlockData],
    records: &[FlowRecord],
    global_name: impl Fn(u32) -> String,
) -> Vec<BackendError> {
    let mut findings: Vec<((BlockId, u32, usize), BackendError)> = Vec::new();
    anchored_escapes(blocks, records, &mut findings);
    global_moves(blocks, records, &global_name, &mut findings);
    findings.sort_by_key(|(key, _)| *key);
    findings.into_iter().map(|(_, error)| error).collect()
}

fn buckets(blocks: &[BlockData], records: &[FlowRecord]) -> Vec<Vec<(u32, FlowEvent)>> {
    let mut events: Vec<Vec<(u32, FlowEvent)>> = vec![Vec::new(); blocks.len()];
    for record in records {
        events[record.block].push((record.index, record.event));
    }
    for bucket in &mut events {
        bucket.sort_by_key(|(index, _)| *index);
    }
    events
}

/// The frame-anchored closure escape analysis: a closure whose owned
/// captures pin it to this frame (an `Anchor` seed) must not outlive
/// the frame. Taint propagates through value copies, closure
/// environments, and block-parameter edges; storing a tainted value in
/// any aggregate, global, cell, or existential — or returning it, or
/// passing it to an owned func-typed parameter (`EscapeSink`) — fails
/// closed with the same diagnostic the builder used to raise inline.
fn anchored_escapes(
    blocks: &[BlockData],
    records: &[FlowRecord],
    findings: &mut Vec<((BlockId, u32, usize), BackendError)>,
) {
    if !records
        .iter()
        .any(|record| matches!(record.event, FlowEvent::Anchor(_)))
    {
        return;
    }
    let events = buckets(blocks, records);
    let hits = |set: &FxHashSet<LocalId>, op: &Operand| {
        matches!(op, Operand::Local(local) if set.contains(local))
    };

    let mut in_states: Vec<Option<FxHashSet<LocalId>>> = vec![None; blocks.len()];
    in_states[0] = Some(FxHashSet::default());
    let mut worklist: Vec<BlockId> = vec![0];
    let mut reported: FxHashSet<(BlockId, u32)> = FxHashSet::default();

    let join = |target: BlockId,
                    incoming: &FxHashSet<LocalId>,
                    in_states: &mut Vec<Option<FxHashSet<LocalId>>>,
                    worklist: &mut Vec<BlockId>| {
        match &mut in_states[target] {
            None => {
                in_states[target] = Some(incoming.clone());
                worklist.push(target);
            }
            Some(existing) => {
                let before = existing.len();
                existing.extend(incoming.iter().copied());
                if existing.len() != before {
                    worklist.push(target);
                }
            }
        }
    };

    while let Some(block) = worklist.pop() {
        let Some(mut taint) = in_states[block].clone() else {
            continue;
        };
        let data = &blocks[block];
        let bucket = &events[block];
        let mut cursor = 0usize;
        let escape = |at: u32, reported: &mut FxHashSet<(BlockId, u32)>,
                          findings: &mut Vec<((BlockId, u32, usize), BackendError)>| {
            if reported.insert((block, at)) {
                findings.push(((block, at, 0), anchored_escape()));
            }
        };

        for (i, inst) in data.insts.iter().enumerate() {
            while cursor < bucket.len() && bucket[cursor].0 <= i as u32 {
                match bucket[cursor].1 {
                    FlowEvent::Anchor(local) => {
                        taint.insert(local);
                    }
                    FlowEvent::EscapeSink(local) => {
                        if taint.contains(&local) {
                            escape(bucket[cursor].0, &mut reported, findings);
                        }
                    }
                    _ => {}
                }
                cursor += 1;
            }
            if taint.is_empty() {
                continue;
            }
            match inst {
                Inst::Copy { dest, src } if hits(&taint, src) => {
                    taint.insert(*dest);
                }
                Inst::MakeClosure { dest, env, .. } if env.iter().any(|op| hits(&taint, op)) => {
                    taint.insert(*dest);
                }
                Inst::Aggregate { tag: 0, args, .. } | Inst::ObjectNew { args, .. }
                    if args.iter().any(|op| hits(&taint, op)) =>
                {
                    escape(i as u32, &mut reported, findings);
                }
                Inst::SetField { src, .. }
                | Inst::ObjectSet { src, .. }
                | Inst::GlobalStore { src, .. }
                | Inst::CellSet { src, .. }
                | Inst::Store { src, .. }
                    if hits(&taint, src) =>
                {
                    escape(i as u32, &mut reported, findings);
                }
                Inst::CellNew { init, .. } if hits(&taint, init) => {
                    escape(i as u32, &mut reported, findings);
                }
                Inst::SetFinalizer { closure, .. } if hits(&taint, closure) => {
                    escape(i as u32, &mut reported, findings);
                }
                Inst::ExistentialPack {
                    payload, witnesses, ..
                } if hits(&taint, payload) || witnesses.iter().any(|op| hits(&taint, op)) => {
                    escape(i as u32, &mut reported, findings);
                }
                Inst::AbortTo { value, .. } if hits(&taint, value) => {
                    escape(i as u32, &mut reported, findings);
                }
                _ => {}
            }
            // Unwind edges carry the taint at the call.
            if let Inst::Call {
                unwind: Some(target),
                ..
            }
            | Inst::CallIndirect {
                unwind: Some(target),
                ..
            } = inst
            {
                join(*target, &taint, &mut in_states, &mut worklist);
            }
        }
        while cursor < bucket.len() {
            match bucket[cursor].1 {
                FlowEvent::Anchor(local) => {
                    taint.insert(local);
                }
                FlowEvent::EscapeSink(local) => {
                    if taint.contains(&local) {
                        escape(bucket[cursor].0, &mut reported, findings);
                    }
                }
                _ => {}
            }
            cursor += 1;
        }

        match &data.term {
            Some(Term::Goto(target, args)) => {
                let mut incoming = taint.clone();
                for (ix, arg) in args.iter().enumerate() {
                    if hits(&taint, arg)
                        && let Some(param) = blocks[*target].params.get(ix)
                    {
                        incoming.insert(*param);
                    }
                }
                join(*target, &incoming, &mut in_states, &mut worklist);
            }
            Some(Term::Branch {
                then_block,
                else_block,
                ..
            }) => {
                for target in [*then_block, *else_block] {
                    join(target, &taint, &mut in_states, &mut worklist);
                }
            }
            Some(Term::Switch {
                targets, default, ..
            }) => {
                for target in targets.iter().copied().chain(std::iter::once(*default)) {
                    join(target, &taint, &mut in_states, &mut worklist);
                }
            }
            Some(Term::Return(value)) => {
                if hits(&taint, value) {
                    escape(u32::MAX, &mut reported, findings);
                }
            }
            Some(Term::Trap(_)) | Some(Term::UnwindRet) | None => {}
        }
    }
}

/// Linear-global move discipline: a linear global consumes exactly once
/// on every path; a reassignment restores it. Joins union (moved on any
/// path stays moved), and a loop's back edge carries the body's moves
/// into the next iteration — the loop-carried case the builder used to
/// detect with a per-loop syntactic scan.
fn global_moves(
    blocks: &[BlockData],
    records: &[FlowRecord],
    global_name: &impl Fn(u32) -> String,
    findings: &mut Vec<((BlockId, u32, usize), BackendError)>,
) {
    if !records
        .iter()
        .any(|record| matches!(record.event, FlowEvent::GlobalMove(_)))
    {
        return;
    }
    let events = buckets(blocks, records);

    let mut in_states: Vec<Option<FxHashSet<u32>>> = vec![None; blocks.len()];
    in_states[0] = Some(FxHashSet::default());
    let mut worklist: Vec<BlockId> = vec![0];
    let mut reported: FxHashSet<(BlockId, u32, u32)> = FxHashSet::default();

    while let Some(block) = worklist.pop() {
        let Some(mut moved) = in_states[block].clone() else {
            continue;
        };
        for (index, event) in &events[block] {
            match event {
                FlowEvent::GlobalMove(slot) => {
                    if !moved.insert(*slot) && reported.insert((block, *index, *slot)) {
                        findings.push((
                            (block, *index, 1),
                            BackendError::new(
                                "use of moved value: this global was already consumed".into(),
                                Span::SYNTHESIZED,
                            ),
                        ));
                    }
                }
                FlowEvent::GlobalRestore(slot) => {
                    moved.remove(slot);
                }
                FlowEvent::GlobalUse(slot, span) => {
                    if moved.contains(slot) && reported.insert((block, *index, *slot)) {
                        findings.push((
                            (block, *index, 1),
                            BackendError::new(
                                format!("use of moved value `{}`", global_name(*slot)),
                                *span,
                            ),
                        ));
                    }
                }
                _ => {}
            }
        }

        let mut join = |target: BlockId| {
            match &mut in_states[target] {
                None => {
                    in_states[target] = Some(moved.clone());
                    worklist.push(target);
                }
                Some(existing) => {
                    let before = existing.len();
                    existing.extend(moved.iter().copied());
                    if existing.len() != before {
                        worklist.push(target);
                    }
                }
            };
        };
        match &blocks[block].term {
            Some(Term::Goto(target, _)) => join(*target),
            Some(Term::Branch {
                then_block,
                else_block,
                ..
            }) => {
                join(*then_block);
                join(*else_block);
            }
            Some(Term::Switch {
                targets, default, ..
            }) => {
                for target in targets.iter().copied().chain(std::iter::once(*default)) {
                    join(target);
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::Constant;
    use super::super::verify::FlowRecord;
    use super::*;

    fn block(insts: Vec<Inst>, term: Term) -> BlockData {
        BlockData {
            debug: None,
            params: Vec::new(),
            insts,
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

    fn ret() -> Term {
        Term::Return(Operand::Const(Constant::Unit))
    }

    #[test]
    fn anchored_closure_returned_is_an_escape() {
        let blocks = vec![block(vec![], Term::Return(Operand::Local(3)))];
        let records = vec![record(0, 0, FlowEvent::Anchor(3))];
        let errors = check(&blocks, &records, |_| String::new());
        assert_eq!(errors.len(), 1, "{errors:?}");
    }

    #[test]
    fn anchored_taint_flows_through_copies_and_goto_params() {
        // b0 anchors L1, copies it to L2, passes L2 as b1's param L5;
        // b1 stores the param into a global.
        let blocks = vec![
            block(
                vec![Inst::Copy {
                    dest: 2,
                    src: Operand::Local(1),
                }],
                Term::Goto(1, vec![Operand::Local(2)]),
            ),
            BlockData {
                debug: None,
                params: vec![5],
                insts: vec![Inst::GlobalStore {
                    global: 0,
                    src: Operand::Local(5),
                }],
                term: Some(ret()),
            },
        ];
        let records = vec![record(0, 0, FlowEvent::Anchor(1))];
        let errors = check(&blocks, &records, |_| String::new());
        assert_eq!(errors.len(), 1, "{errors:?}");
    }

    #[test]
    fn unanchored_closures_report_nothing() {
        let blocks = vec![block(
            vec![Inst::GlobalStore {
                global: 0,
                src: Operand::Local(1),
            }],
            ret(),
        )];
        assert!(check(&blocks, &[], |_| String::new()).is_empty());
    }

    #[test]
    fn escape_sink_fires_only_for_tainted_locals() {
        let blocks = vec![block(vec![], ret())];
        let clean = vec![record(0, 0, FlowEvent::EscapeSink(4))];
        assert!(check(&blocks, &clean, |_| String::new()).is_empty());
        let tainted = vec![
            record(0, 0, FlowEvent::Anchor(4)),
            record(0, 0, FlowEvent::EscapeSink(4)),
        ];
        assert_eq!(check(&blocks, &tainted, |_| String::new()).len(), 1);
    }

    #[test]
    fn global_double_consume_is_reported_once() {
        let blocks = vec![block(vec![], ret())];
        let records = vec![
            record(0, 0, FlowEvent::GlobalMove(7)),
            record(0, 1, FlowEvent::GlobalMove(7)),
        ];
        let errors = check(&blocks, &records, |_| "g".into());
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].message.contains("already consumed"), "{errors:?}");
    }

    #[test]
    fn global_use_after_move_names_the_global() {
        let blocks = vec![block(vec![], ret())];
        let records = vec![
            record(0, 0, FlowEvent::GlobalMove(7)),
            record(0, 1, FlowEvent::GlobalUse(7, Span::SYNTHESIZED)),
        ];
        let errors = check(&blocks, &records, |_| "counter".into());
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].message.contains("use of moved value `counter`"),
            "{errors:?}"
        );
    }

    #[test]
    fn global_restore_clears_the_move() {
        let blocks = vec![block(vec![], ret())];
        let records = vec![
            record(0, 0, FlowEvent::GlobalMove(7)),
            record(0, 1, FlowEvent::GlobalRestore(7)),
            record(0, 2, FlowEvent::GlobalUse(7, Span::SYNTHESIZED)),
            record(0, 3, FlowEvent::GlobalMove(7)),
        ];
        assert!(check(&blocks, &records, |_| "g".into()).is_empty());
    }

    #[test]
    fn loop_carried_global_move_is_reported() {
        // b0 -> b1 (loop head) -> b2 (body: use then move) -> b1; b1 -> b3 exit.
        let blocks = vec![
            block(vec![], Term::Goto(1, vec![])),
            block(
                vec![],
                Term::Branch {
                    cond: Operand::Local(0),
                    then_block: 2,
                    else_block: 3,
                },
            ),
            block(vec![], Term::Goto(1, vec![])),
            block(vec![], ret()),
        ];
        let records = vec![
            record(2, 0, FlowEvent::GlobalUse(7, Span::SYNTHESIZED)),
            record(2, 1, FlowEvent::GlobalMove(7)),
        ];
        let errors = check(&blocks, &records, |_| "g".into());
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("use of moved value `g`")),
            "the second iteration's read sees the first iteration's move: {errors:?}"
        );
    }
}
