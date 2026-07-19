//! Release placement: every control-flow release derived from the CFG,
//! replacing the per-construct bookkeeping (scope stacks, arm-merge
//! divergence, cleanup-chain healing) that each construct had to
//! re-implement and could get wrong — the completion of wave C in
//! docs/ownership-rethink-plan.md. The model is Rust's MIR drop
//! elaboration: drops derived from an initialization fixpoint, here the
//! same forward replay the balance verifier runs.
//!
//! Placement is the *required* set, nothing eager:
//!
//! - **frame exits**: everything owned at a `Return`/`UnwindRet` block's
//!   end releases there — the old scope-exit timing, frame-wide;
//! - **equalization edges**: where a join would receive a value owned on
//!   one predecessor and gone on another, the owned predecessors release
//!   on their edges in — exactly the divergence the old merge machinery
//!   hand-computed per construct, including the per-iteration death of
//!   loop bindings at the back edge;
//! - **per-call unwind sets**: the owned values at each call site, from
//!   which the unwind chains are built.
//!
//! Values are never released before their last use because they are
//! never released before the frame or path ends at all — which is why
//! this needs no liveness and no view provenance: a non-owning view can
//! never outlive its root's frame-timed release. Eager frontier
//! placement (Perceus: Reinking, Xie, de Moura & Leijen, PLDI 2021)
//! becomes sound wholesale once owning stored views land, and slots in
//! here when it does.
//!
//! `Trap` exits release nothing: a trap aborts the program, not the
//! frame. Point releases that belong to a single expression — a
//! reassignment destroying the displaced old value, an unbound match
//! payload — stay the builder's, placed where the expression happens;
//! this module owns everything whose position is a property of the
//! control-flow graph.

use super::verify::{self, FlowEvent, FlowRecord, OWNED};
use super::{BlockData, BlockId, Inst, LocalId, Term};

/// Where a function's releases belong. Blocks index `end_of_block`.
#[derive(Debug, Default, PartialEq, Eq)]
pub(super) struct Plan {
    /// Locals to release just before a frame-exit block's terminator,
    /// in reverse-definition order.
    pub end_of_block: Vec<Vec<LocalId>>,
    /// Equalization releases: `(from, successor position, locals)` —
    /// released on that edge, emitted by splitting it. Successor
    /// positions count Goto as 0 and Branch as then 0 / else 1.
    pub edges: Vec<(BlockId, usize, Vec<LocalId>)>,
    /// For each call position `(block, instruction index)`, the owned
    /// locals at that point — the live set an unwind chain must
    /// release.
    pub unwind_live: Vec<((BlockId, u32), Vec<LocalId>)>,
}

/// Compute the release plan for one function from its blocks and the
/// ownership event log.
pub(super) fn plan(blocks: &[BlockData], records: &[FlowRecord]) -> Plan {
    let n_locals = records
        .iter()
        .map(|record| {
            let (FlowEvent::Def(l) | FlowEvent::Use(l) | FlowEvent::Move(l) | FlowEvent::Drop(l)) =
                record.event;
            l as usize + 1
        })
        .max()
        .unwrap_or(0);
    let mut plan = Plan {
        end_of_block: vec![Vec::new(); blocks.len()],
        edges: Vec::new(),
        unwind_live: Vec::new(),
    };
    if n_locals == 0 {
        return plan;
    }

    // Ownership at each block entry, from the verifier's fixpoint, then
    // replayed forward for per-call owned sets and block-end states.
    let entry_states = verify::entry_states(blocks, records);
    let mut events: Vec<Vec<(u32, FlowEvent)>> = vec![Vec::new(); blocks.len()];
    for record in records {
        events[record.block].push((record.index, record.event));
    }
    for bucket in &mut events {
        bucket.sort_by_key(|(index, _)| *index);
    }
    let mut owned_at_end: Vec<Option<Vec<u8>>> = vec![None; blocks.len()];
    for (id, block) in blocks.iter().enumerate() {
        let Some(mut state) = entry_states.get(id).and_then(|state| state.clone()) else {
            continue;
        };
        let mut cursor = 0usize;
        let bucket = &events[id];
        for (i, inst) in block.insts.iter().enumerate() {
            while cursor < bucket.len() && bucket[cursor].0 <= i as u32 {
                apply(bucket[cursor].1, &mut state);
                cursor += 1;
            }
            if matches!(inst, Inst::Call { .. } | Inst::CallIndirect { .. }) {
                let owned: Vec<LocalId> = (0..n_locals)
                    .filter(|local| state[*local] == OWNED)
                    .map(|local| local as LocalId)
                    .collect();
                if !owned.is_empty() {
                    plan.unwind_live.push(((id, i as u32), owned));
                }
            }
        }
        while cursor < bucket.len() {
            apply(bucket[cursor].1, &mut state);
            cursor += 1;
        }
        owned_at_end[id] = Some(state);
    }

    // Frame exits release everything owned.
    for (id, block) in blocks.iter().enumerate() {
        let Some(state) = owned_at_end.get(id).and_then(|state| state.as_ref()) else {
            continue;
        };
        if matches!(block.term, Some(Term::Return(_)) | Some(Term::UnwindRet)) {
            for local in (0..n_locals).rev() {
                if state[local] == OWNED {
                    plan.end_of_block[id].push(local as LocalId);
                }
            }
        }
    }

    // A discontinue (`AbortTo`) leaves the frame mid-block and never
    // returns control: everything the predecessor still owns releases
    // on the edge in, exactly like a frame exit — the code after the
    // abort never runs, so releases cannot go inside the block.
    let aborts: Vec<bool> = blocks
        .iter()
        .map(|block| {
            block
                .insts
                .iter()
                .any(|inst| matches!(inst, Inst::AbortTo { .. }))
        })
        .collect();

    // Equalization: a join must not receive a value owned on one edge
    // and gone on another. Gather each block's terminator predecessors;
    // where ownership disagrees, the owned edges release on the way in.
    let mut pred_edges: Vec<Vec<(BlockId, usize)>> = vec![Vec::new(); blocks.len()];
    for (id, block) in blocks.iter().enumerate() {
        match &block.term {
            Some(Term::Goto(target, _)) => pred_edges[*target].push((id, 0)),
            Some(Term::Branch {
                then_block,
                else_block,
                ..
            }) => {
                pred_edges[*then_block].push((id, 0));
                pred_edges[*else_block].push((id, 1));
            }
            _ => {}
        }
    }
    let mut edge_keys: Vec<(BlockId, usize)> = Vec::new();
    let mut edge_releases: Vec<Vec<LocalId>> = Vec::new();
    for (target, preds) in pred_edges.iter().enumerate() {
        if aborts[target] {
            for (pred, position) in preds {
                let Some(state) = owned_at_end.get(*pred).and_then(|state| state.as_ref()) else {
                    continue;
                };
                let locals: Vec<LocalId> = (0..n_locals)
                    .rev()
                    .filter(|local| state[*local] == OWNED)
                    .map(|local| local as LocalId)
                    .collect();
                if !locals.is_empty() {
                    edge_keys.push((*pred, *position));
                    edge_releases.push(locals);
                }
            }
            continue;
        }
        if preds.len() < 2 {
            continue;
        }
        for local in (0..n_locals).rev() {
            let states: Vec<u8> = preds
                .iter()
                .filter_map(|(pred, _)| {
                    owned_at_end
                        .get(*pred)
                        .and_then(|state| state.as_ref())
                        .map(|state| state[local])
                })
                .collect();
            // Unreachable predecessors contribute no state: their
            // edges never run, so they cannot disagree.
            let any_owned = states.contains(&OWNED);
            let all_owned = states.iter().all(|state| *state == OWNED);
            if !any_owned || all_owned {
                continue;
            }
            for (pred, position) in preds {
                let owned = owned_at_end
                    .get(*pred)
                    .and_then(|state| state.as_ref())
                    .is_some_and(|state| state[local] == OWNED);
                if !owned {
                    continue;
                }
                let key = (*pred, *position);
                match edge_keys.iter().position(|existing| *existing == key) {
                    Some(at) => edge_releases[at].push(local as LocalId),
                    None => {
                        edge_keys.push(key);
                        edge_releases.push(vec![local as LocalId]);
                    }
                }
            }
        }
    }
    for (key, locals) in edge_keys.into_iter().zip(edge_releases) {
        plan.edges.push((key.0, key.1, locals));
    }
    plan
}

fn apply(event: FlowEvent, state: &mut [u8]) {
    match event {
        FlowEvent::Def(local) => state[local as usize] = OWNED,
        FlowEvent::Move(local) | FlowEvent::Drop(local) => {
            state[local as usize] = verify::DEAD;
        }
        FlowEvent::Use(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Constant, Operand};
    use super::*;

    fn record(block: BlockId, index: u32, event: FlowEvent) -> FlowRecord {
        FlowRecord {
            block,
            index,
            event,
        }
    }

    fn ret_block(insts: Vec<Inst>) -> BlockData {
        BlockData {
            params: Vec::new(),
            insts,
            term: Some(Term::Return(Operand::Const(Constant::Unit))),
        }
    }

    #[test]
    fn straight_line_owned_value_releases_at_the_exit_block_end() {
        let blocks = vec![ret_block(vec![Inst::Copy {
            dest: 1,
            src: Operand::Const(Constant::Unit),
        }])];
        let records = vec![record(0, 1, FlowEvent::Def(1))];
        let plan = plan(&blocks, &records);
        assert_eq!(plan.end_of_block[0], vec![1]);
        assert!(plan.edges.is_empty());
    }

    #[test]
    fn moved_values_release_nowhere() {
        let blocks = vec![ret_block(vec![Inst::Copy {
            dest: 1,
            src: Operand::Const(Constant::Unit),
        }])];
        let records = vec![
            record(0, 1, FlowEvent::Def(1)),
            record(0, 1, FlowEvent::Move(1)),
        ];
        let plan = plan(&blocks, &records);
        assert!(plan.end_of_block[0].is_empty());
    }

    #[test]
    fn a_join_of_owned_and_moved_paths_equalizes_on_the_owned_edge() {
        // b0 defines local 1, branches to b1 (moves it) and b2 (never
        // touches it); both goto b3 which returns. The b2 path still
        // owns the value at the join, so its edge into b3 releases —
        // the divergence the old merge machinery hand-computed.
        let blocks = vec![
            BlockData {
                params: Vec::new(),
                insts: vec![Inst::Copy {
                    dest: 1,
                    src: Operand::Const(Constant::Unit),
                }],
                term: Some(Term::Branch {
                    cond: Operand::Local(9),
                    then_block: 1,
                    else_block: 2,
                }),
            },
            BlockData {
                params: Vec::new(),
                insts: vec![Inst::Copy {
                    dest: 2,
                    src: Operand::Local(1),
                }],
                term: Some(Term::Goto(3, Vec::new())),
            },
            BlockData {
                params: Vec::new(),
                insts: Vec::new(),
                term: Some(Term::Goto(3, Vec::new())),
            },
            ret_block(Vec::new()),
        ];
        let records = vec![
            record(0, 1, FlowEvent::Def(1)),
            record(1, 1, FlowEvent::Move(1)),
        ];
        let plan = plan(&blocks, &records);
        assert_eq!(plan.edges, vec![(2, 0, vec![1])], "{plan:?}");
        assert!(plan.end_of_block[3].is_empty());
    }

    #[test]
    fn calls_carry_the_owned_set_for_their_unwind_chain() {
        let blocks = vec![ret_block(vec![
            Inst::Copy {
                dest: 1,
                src: Operand::Const(Constant::Unit),
            },
            Inst::Call {
                dest: 2,
                func: 0,
                args: Vec::new(),
                unwind: None,
            },
        ])];
        let records = vec![record(0, 1, FlowEvent::Def(1))];
        let plan = plan(&blocks, &records);
        assert_eq!(plan.unwind_live, vec![((0, 1), vec![1])]);
    }

    #[test]
    fn loop_bindings_die_on_the_back_edge() {
        // b0 enters loop head b1; body b2 defines local 1 fresh each
        // iteration and loops back; exit b3 returns. The back edge owns
        // the value while first entry does not: the equalization
        // release on the back edge is the per-iteration death the old
        // in-loop scope drops provided.
        let blocks = vec![
            BlockData {
                params: Vec::new(),
                insts: Vec::new(),
                term: Some(Term::Goto(1, Vec::new())),
            },
            BlockData {
                params: Vec::new(),
                insts: Vec::new(),
                term: Some(Term::Branch {
                    cond: Operand::Local(9),
                    then_block: 2,
                    else_block: 3,
                }),
            },
            BlockData {
                params: Vec::new(),
                insts: vec![Inst::Copy {
                    dest: 1,
                    src: Operand::Const(Constant::Unit),
                }],
                term: Some(Term::Goto(1, Vec::new())),
            },
            ret_block(Vec::new()),
        ];
        let records = vec![record(2, 1, FlowEvent::Def(1))];
        let plan = plan(&blocks, &records);
        assert_eq!(plan.edges, vec![(2, 0, vec![1])], "{plan:?}");
    }

    #[test]
    fn values_owned_through_a_loop_release_at_the_exit() {
        // b0 defines local 1 and enters loop head b1; body b2 reads it
        // and loops back; exit b3 returns. Both edges into the head own
        // the value (no equalization), so the only release is the
        // frame exit.
        let blocks = vec![
            BlockData {
                params: Vec::new(),
                insts: vec![Inst::Copy {
                    dest: 1,
                    src: Operand::Const(Constant::Unit),
                }],
                term: Some(Term::Goto(1, Vec::new())),
            },
            BlockData {
                params: Vec::new(),
                insts: Vec::new(),
                term: Some(Term::Branch {
                    cond: Operand::Local(9),
                    then_block: 2,
                    else_block: 3,
                }),
            },
            BlockData {
                params: Vec::new(),
                insts: vec![Inst::Copy {
                    dest: 2,
                    src: Operand::Local(1),
                }],
                term: Some(Term::Goto(1, Vec::new())),
            },
            ret_block(Vec::new()),
        ];
        let records = vec![record(0, 1, FlowEvent::Def(1))];
        let plan = plan(&blocks, &records);
        assert!(plan.edges.is_empty(), "{plan:?}");
        assert_eq!(plan.end_of_block[3], vec![1]);
    }
}
