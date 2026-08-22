//! The ownership elaborator: the MIR rewrite's core (docs/ownership.md,
//! realized). The lowering walk no longer decides retain-vs-move — it
//! records ownership SITES (consumes, displacements, writeback bases,
//! loans, owned reads) and emits no ownership instructions or events at
//! them. This pass runs over the finished control-flow graph:
//!
//! 1. **Liveness** is computed backward over the blocks — real uses on
//!    real paths, loop-carried across back edges, views folded into
//!    their roots through the recorded borrow edges. This one analysis
//!    replaces the walk's syntactic `use_counts`, the `loop_depth`
//!    heuristics (Wave D's placeholder), and the live-view scans.
//! 2. **A forward replay** walks sites and events in CFG order carrying
//!    per-local owned-ness, decides every site (donate / move / drop /
//!    displace), raises the user diagnostics the walk used to raise
//!    inline (use-after-move, move-while-mut-borrowed, second consume of
//!    a linear value, view-after-owner-moved), and appends the
//!    Def/Use/Move/Drop events the release planner and balance verifier
//!    consume.
//! 3. **Realization** inserts the decided instructions (retains as one
//!    instruction per site — pointer retains, region claims, witness
//!    calls, or a `Glue::Retain` call for aggregates; drops via
//!    `Glue::Drop`), then remaps every event index across the
//!    insertions.
//!
//! A construct added to the walk gets ownership by recording a site; it
//! cannot forget a merge, a loop, or a sibling path, because those come
//! from the graph, not from the walk.

use rustc_hash::{FxHashMap, FxHashSet};

use super::verify::{FlowEvent, FlowRecord};
use super::{
    BackendError, BlockId, FunctionBuilder, Glue, Inst, LocalId, Operand, Span, Term, Ty,
    contains_object, donates, is_linear, needs_drop,
};
use crate::name_resolution::symbol::Symbol;

/// Why a consume can never donate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Forced {
    /// The value is linear: a second reference is what linearity forbids.
    Linear,
    /// The local is a `*T` parameter: statically the sole reference.
    Unique,
    /// Return position: the frame's value moves out, never donates.
    Return,
}

#[derive(Clone, Debug)]
pub(super) enum SiteKind {
    /// Ownership transfers into a callee/binding/join.
    Consume { forced: Option<Forced> },
    /// A reassignment replaced the local's value: drop the old value,
    /// or displace it to scope exit while a view still reads it.
    Displace,
    /// A `mut` call writeback replaces the base: under a live view,
    /// retain and displace the pre-call value.
    Writeback,
}

#[derive(Clone, Debug)]
pub(super) struct OwnershipSite {
    pub block: BlockId,
    /// Global walk order (shared counter with `flow_events`): replay
    /// must interleave events, reads, and sites exactly as the walk
    /// emitted them.
    pub seq: u32,
    /// Instruction position the site precedes (the walk records
    /// `insts.len()` before pushing the consuming instruction).
    pub index: u32,
    pub local: LocalId,
    pub ty: Ty,
    pub kind: SiteKind,
    pub span: Span,
}

/// A read of a tracked owned local or view (the named-variable path):
/// where the walk used to raise use-after-move inline.
#[derive(Clone, Debug)]
pub(super) struct ReadSite {
    pub block: BlockId,
    /// Global walk order (shared counter with `flow_events`): replay
    /// must interleave events, reads, and sites exactly as the walk
    /// emitted them.
    pub seq: u32,
    pub index: u32,
    pub local: LocalId,
    pub name: String,
    pub span: Span,
}

/// A borrow with a named view binding; exclusivity checks key off it.
#[derive(Clone, Debug)]
pub(super) struct LoanSite {
    pub block: BlockId,
    /// Global walk order (shared counter with `flow_events`): replay
    /// must interleave events, reads, and sites exactly as the walk
    /// emitted them.
    pub seq: u32,
    pub root: LocalId,
    pub view: LocalId,
    pub view_name: String,
    pub exclusive: bool,
}

#[derive(Default)]
pub(super) struct OwnershipSites {
    pub sites: Vec<OwnershipSite>,
    pub reads: Vec<ReadSite>,
    pub loans: Vec<LoanSite>,
    /// Loan kills, as `(seq, root)`: a writeback invalidates every loan
    /// rooted at base.
    pub loan_kills: Vec<(u32, LocalId)>,
    /// Walk-order stamps for `flow_events`, index-aligned.
    pub event_seqs: Vec<u32>,
    /// The shared walk-order counter.
    pub next_seq: u32,
}

/// One decided instruction insertion: `insts` go before the site's
/// instruction position.
struct Insertion {
    block: BlockId,
    index: u32,
    insts: Vec<Inst>,
}

const OWNED: u8 = 1;

impl FunctionBuilder<'_, '_> {
    fn locals_len(&self) -> usize {
        usize::from(self.n_locals()).max(
            self.frame
                .iter()
                .enumerate()
                .map(|(index, _)| index + 1)
                .last()
                .unwrap_or(0),
        )
    }

    /// view → root edges for genuinely view-typed locals.
    fn view_edges(&self) -> FxHashMap<LocalId, LocalId> {
        self.borrow_roots
            .iter()
            .filter(|(view, _)| self.view_locals.contains(*view))
            .map(|(view, root)| (*view, *root))
            .collect()
    }

    /// Whether a local ever held a tracked owned value.
    fn tracks(&self, local: LocalId) -> bool {
        self.frame
            .get(usize::from(local))
            .is_some_and(|entry| entry.owned.is_some())
    }

    fn view_root_of(&self, local: LocalId) -> Option<LocalId> {
        if !self.view_locals.contains(&local) {
            return None;
        }
        self.borrow_roots.get(&local).copied()
    }

    /// A fresh scope-owned local for a displaced value: the release
    /// planner drops it at frame exits from its Def event.
    fn mint_displaced(&mut self, ty: &Ty) -> LocalId {
        let displaced = self.fresh_local();
        let entry = self.frame_entry(displaced);
        entry.owned = Some(ty.clone());
        displaced
    }

    fn generated_origin_debug(&self) -> super::DebugOrigin {
        super::DebugOrigin::Generated(self.generated_origin)
    }

    /// The instruction sequence that donates one reference to `value`
    /// of type `ty` — straight-line by construction: aggregates and
    /// enums retain through their synthesized `Glue::Retain` function.
    /// The walk's `retain_value` realizes through here too — one
    /// realization path for walk-side and replay-decided retains.
    pub(super) fn realize_retain(
        &mut self,
        value: Operand,
        ty: &Ty,
        span: Span,
    ) -> Result<Vec<Inst>, BackendError> {
        let mut ty = self.resolved(ty);
        while let Ty::Borrow(_, inner) = ty {
            ty = *inner;
        }
        Ok(match &ty {
            Ty::Any { .. } => {
                let witness = self.fresh_local();
                let payload = self.fresh_local();
                let dest = self.fresh_local();
                vec![
                    Inst::ExistentialWitness {
                        dest: witness,
                        src: value,
                        index: 1,
                    },
                    Inst::ExistentialPayload {
                        dest: payload,
                        src: value,
                    },
                    Inst::CallIndirect {
                        dest,
                        callee: Operand::Local(witness),
                        args: vec![Operand::Local(payload)],
                        unwind: None,
                    },
                ]
            }
            Ty::Param(symbol) => {
                let Some((_, retain_witness)) = self.param_witnesses.get(symbol).copied() else {
                    return Err(BackendError::unsupported(
                        "a generic value cannot be retained here without its ownership witnesses (not supported yet)"
                            .into(),
                        span,
                    ));
                };
                let dest = self.fresh_local();
                vec![Inst::CallIndirect {
                    dest,
                    callee: Operand::Local(retain_witness),
                    args: vec![value],
                    unwind: None,
                }]
            }
            Ty::Nominal(symbol, _) if *symbol == Symbol::RawPtr => {
                vec![Inst::RetainPtr { src: value }]
            }
            Ty::Nominal(symbol, _)
                if self
                    .program_builder
                    .struct_def(*symbol)
                    .is_some_and(|def| def.heap) =>
            {
                vec![Inst::RegionAcquire { src: value }]
            }
            Ty::Nominal(..) | Ty::Tuple(_) | Ty::Record(_)
                if donates(self.program_builder, &ty) =>
            {
                let func = self.program_builder.value_glue(&ty, Glue::Retain)?;
                let dest = self.fresh_local();
                vec![Inst::Call {
                    dest,
                    func,
                    args: vec![value],
                    unwind: None,
                }]
            }
            _ => Vec::new(),
        })
    }

    /// The instruction sequence that releases a displaced value: region
    /// claims first, then the type's synthesized `Glue::Drop`.
    fn realize_drop(
        &mut self,
        local: LocalId,
        ty: &Ty,
        span: Span,
    ) -> Result<Vec<Inst>, BackendError> {
        let mut resolved = self.resolved(ty);
        while let Ty::Borrow(_, inner) = resolved {
            resolved = *inner;
        }
        if is_linear(self.program_builder, &resolved) && !self.in_unwind_cleanup {
            return Err(BackendError::new(
                format!(
                    "a linear `{}` value must be consumed exactly once on every path",
                    resolved.render_mono()
                ),
                span,
            ));
        }
        let mut insts = Vec::new();
        let value = Operand::Local(local);
        if contains_object(self.program_builder, &resolved) {
            insts.push(Inst::RegionRelease { src: value });
            if let Ty::Nominal(symbol, _) = &resolved
                && self
                    .program_builder
                    .struct_def(*symbol)
                    .is_some_and(|def| def.heap)
            {
                return Ok(insts);
            }
        }
        if needs_drop(self.program_builder, &resolved) {
            match &resolved {
                Ty::Any { .. } => {
                    let witness = self.fresh_local();
                    let payload = self.fresh_local();
                    let dest = self.fresh_local();
                    insts.extend([
                        Inst::ExistentialWitness {
                            dest: witness,
                            src: value,
                            index: 0,
                        },
                        Inst::ExistentialPayload {
                            dest: payload,
                            src: value,
                        },
                        Inst::CallIndirect {
                            dest,
                            callee: Operand::Local(witness),
                            args: vec![Operand::Local(payload)],
                            unwind: None,
                        },
                    ]);
                }
                Ty::Param(symbol) => {
                    let Some((drop_witness, _)) = self.param_witnesses.get(symbol).copied() else {
                        return Err(BackendError::unsupported(
                            "a generic value cannot be released here without its ownership witnesses (not supported yet)"
                                .into(),
                            span,
                        ));
                    };
                    let dest = self.fresh_local();
                    insts.push(Inst::CallIndirect {
                        dest,
                        callee: Operand::Local(drop_witness),
                        args: vec![value],
                        unwind: None,
                    });
                }
                _ => {
                    let func = self.program_builder.value_glue(&resolved, Glue::Drop)?;
                    let dest = self.fresh_local();
                    insts.push(Inst::Call {
                        dest,
                        func,
                        args: vec![value],
                        unwind: None,
                    });
                }
            }
        }
        Ok(insts)
    }

    /// Run the elaboration: decide every recorded site, insert the
    /// decided instructions, append ownership events, and raise the
    /// walk's former inline diagnostics. Must run before the release
    /// planner and the balance verifier.
    pub(super) fn elaborate_ownership(&mut self) {
        let sites = std::mem::take(&mut self.ownership_sites);
        if sites.sites.is_empty() && sites.reads.is_empty() && sites.loans.is_empty() {
            return;
        }
        let n_locals = self.locals_len();
        let live = Liveness::compute(
            &self.blocks,
            n_locals,
            &self.view_edges(),
            &sites,
            &sites.event_seqs,
            &self.flow_events,
        );

        // --- Forward replay: owned-ness per local, decisions per site.
        #[derive(Clone, Copy)]
        enum Agenda<'s> {
            Site(&'s OwnershipSite),
            Read(&'s ReadSite),
            Event(FlowEvent),
        }
        // Bucket the agenda per block, stable-ordered by index (events
        // and sites recorded in walk order stay in walk order).
        let mut agenda: Vec<Vec<((u32, u32), Agenda)>> = vec![Vec::new(); self.blocks.len()];
        for (position, record) in self.flow_events.iter().enumerate() {
            let seq = sites.event_seqs.get(position).copied().unwrap_or(u32::MAX);
            agenda[record.block].push(((record.index, seq), Agenda::Event(record.event)));
        }
        for read in &sites.reads {
            agenda[read.block].push(((read.index, read.seq), Agenda::Read(read)));
        }
        for site in &sites.sites {
            agenda[site.block].push(((site.index, site.seq), Agenda::Site(site)));
        }
        for bucket in &mut agenda {
            bucket.sort_by_key(|(key, _)| *key);
        }

        // Decisions accumulate here; realization happens after the replay
        // so instruction indices stay stable throughout.
        let mut insertions: Vec<Insertion> = Vec::new();
        let mut new_events: Vec<(u32, FlowRecord)> = Vec::new();
        let mut errors: Vec<(u32, BackendError)> = Vec::new();
        // Loans alive per path are approximated flow-insensitively: a
        // loan is active at P if its creation precedes P in the agenda
        // walk of P's block or a dominating one, it is not killed, and
        // its view is live at P. Path-precision comes from view
        // liveness; creation order is a proxy the corpus adjudicates.
        let loan_active = |query_seq: u32, site_block: BlockId, site_index: u32, root: LocalId| {
            if !live.view_live_site(query_seq) {
                return None;
            }
            let _ = (site_block, site_index);
            sites.loans.iter().find(|loan| {
                loan.root == root
                    && loan.seq <= query_seq
                    && !sites.loan_kills.iter().any(|(kill_seq, kill_root)| {
                        *kill_root == root && loan.seq <= *kill_seq && *kill_seq <= query_seq
                    })
            })
        };

        let mut in_states: Vec<Option<Vec<u8>>> = vec![None; self.blocks.len()];
        in_states[0] = Some(vec![0; n_locals]);
        let mut worklist: Vec<BlockId> = vec![0];
        let mut decided: FxHashSet<u32> = FxHashSet::default();
        let mut reported: FxHashSet<(BlockId, u32)> = FxHashSet::default();

        while let Some(block) = worklist.pop() {
            let Some(mut state) = in_states[block].clone() else {
                continue;
            };
            for ((index, entry_seq), entry) in &agenda[block] {
                let entry_seq = *entry_seq;
                match entry {
                    Agenda::Event(event) => match event {
                        FlowEvent::Def(local) => state[*local as usize] = OWNED,
                        FlowEvent::Move(local) | FlowEvent::Drop(local) => {
                            state[*local as usize] = 0
                        }
                        _ => {}
                    },
                    Agenda::Read(read) => {
                        let owned = state[read.local as usize] == OWNED;
                        if !owned && self.tracks(read.local) && reported.insert((block, *index)) {
                            // The walk's former hard errors, in priority
                            // order: a view whose owner moved, then a
                            // plain use-after-move.
                            if let Some(root) = self.view_root_of(read.local) {
                                if state[root as usize] != OWNED {
                                    errors.push((
                                        entry_seq,
                                        BackendError::new(
                                            format!(
                                                "use of borrowed value `{}`: its owner was moved",
                                                read.name
                                            ),
                                            read.span,
                                        ),
                                    ));
                                    continue;
                                }
                            }
                            errors.push((
                                entry_seq,
                                BackendError::new(
                                    format!("use of moved value `{}`", read.name),
                                    read.span,
                                ),
                            ));
                        } else if owned
                            && let Some(loan) = loan_active(read.seq, block, *index, read.local)
                                .filter(|l| l.exclusive)
                            && loan.view != read.local
                            && reported.insert((block, *index))
                        {
                            errors.push((
                                entry_seq,
                                BackendError::new(
                                    format!(
                                        "`{}` is already mutable borrowed as `{}`",
                                        read.name, loan.view_name
                                    ),
                                    read.span,
                                ),
                            ));
                        }
                    }
                    Agenda::Site(site) => {
                        let key = site.seq;
                        let owned = state[site.local as usize] == OWNED;
                        match &site.kind {
                            SiteKind::Consume { forced } => {
                                let live_after = live.after_site(site.seq);
                                let donate = match forced {
                                    Some(_) => {
                                        if !owned && reported.insert((block, *index)) {
                                            errors.push((entry_seq, BackendError::new(
                                                "use of moved value: consumed twice in one call"
                                                    .into(),
                                                Span::SYNTHESIZED,
                                            )));
                                        }
                                        false
                                    }
                                    None if !self.can_release(&site.ty) => false,
                                    None => live_after || !owned,
                                };
                                if !donate
                                    && owned
                                    && let Some(loan) =
                                        loan_active(site.seq, block, *index, site.local)
                                            .filter(|l| l.exclusive)
                                    && reported.insert((block, *index))
                                {
                                    errors.push((
                                        entry_seq,
                                        BackendError::new(
                                            format!(
                                                "cannot move a value while it is borrowed as `{}`",
                                                loan.view_name
                                            ),
                                            Span::SYNTHESIZED,
                                        ),
                                    ));
                                }
                                if decided.insert(key) {
                                    if donate {
                                        let respend = !owned;
                                        let retain = self.realize_retain(
                                            Operand::Local(site.local),
                                            &site.ty,
                                            site.span,
                                        );
                                        match retain {
                                            Ok(insts) => insertions.push(Insertion {
                                                block,
                                                index: *index,
                                                insts,
                                            }),
                                            Err(error) => errors.push((entry_seq, error)),
                                        }
                                        if respend {
                                            new_events.push((
                                                site.seq,
                                                FlowRecord {
                                                    block,
                                                    index: *index,
                                                    event: FlowEvent::Def(site.local),
                                                },
                                            ));
                                            new_events.push((
                                                site.seq,
                                                FlowRecord {
                                                    block,
                                                    index: *index,
                                                    event: FlowEvent::Move(site.local),
                                                },
                                            ));
                                        } else {
                                            new_events.push((
                                                site.seq,
                                                FlowRecord {
                                                    block,
                                                    index: *index,
                                                    event: FlowEvent::Use(site.local),
                                                },
                                            ));
                                        }
                                    } else {
                                        new_events.push((
                                            site.seq,
                                            FlowRecord {
                                                block,
                                                index: *index,
                                                event: FlowEvent::Move(site.local),
                                            },
                                        ));
                                    }
                                }
                                if !donate {
                                    state[site.local as usize] = 0;
                                }
                            }
                            SiteKind::Displace => {
                                if !owned {
                                    continue;
                                }
                                let view_live = live.view_live_site(site.seq);
                                if decided.insert(key) {
                                    if view_live {
                                        let displaced = self.mint_displaced(&site.ty);
                                        insertions.push(Insertion {
                                            block,
                                            index: *index,
                                            insts: vec![Inst::Copy {
                                                dest: displaced,
                                                src: Operand::Local(site.local),
                                            }],
                                        });
                                        new_events.push((
                                            site.seq,
                                            FlowRecord {
                                                block,
                                                index: *index,
                                                event: FlowEvent::Move(site.local),
                                            },
                                        ));
                                        new_events.push((
                                            site.seq,
                                            FlowRecord {
                                                block,
                                                index: *index,
                                                event: FlowEvent::Def(displaced),
                                            },
                                        ));
                                    } else {
                                        new_events.push((
                                            site.seq,
                                            FlowRecord {
                                                block,
                                                index: *index,
                                                event: FlowEvent::Drop(site.local),
                                            },
                                        ));
                                        match self.realize_drop(site.local, &site.ty, site.span) {
                                            Ok(insts) => insertions.push(Insertion {
                                                block,
                                                index: *index,
                                                insts,
                                            }),
                                            Err(error) => errors.push((entry_seq, error)),
                                        }
                                    }
                                }
                                state[site.local as usize] = 0;
                            }
                            SiteKind::Writeback => {
                                if !owned {
                                    continue;
                                }
                                let view_live = live.view_live_site(site.seq);
                                if decided.insert(key) && view_live {
                                    let mut insts = match self.realize_retain(
                                        Operand::Local(site.local),
                                        &site.ty,
                                        site.span,
                                    ) {
                                        Ok(insts) => insts,
                                        Err(error) => {
                                            errors.push((entry_seq, error));
                                            Vec::new()
                                        }
                                    };
                                    let displaced = self.mint_displaced(&site.ty);
                                    insts.push(Inst::Copy {
                                        dest: displaced,
                                        src: Operand::Local(site.local),
                                    });
                                    insertions.push(Insertion {
                                        block,
                                        index: *index,
                                        insts,
                                    });
                                    new_events.push((
                                        site.seq,
                                        FlowRecord {
                                            block,
                                            index: *index,
                                            event: FlowEvent::Def(displaced),
                                        },
                                    ));
                                }
                            }
                        }
                    }
                }
            }

            // Propagate to successors (any-path owned: a join where one
            // path moved is settled by the release planner's edge
            // equalization, exactly as before).
            let push = |target: BlockId,
                        in_states: &mut Vec<Option<Vec<u8>>>,
                        worklist: &mut Vec<BlockId>| {
                match &mut in_states[target] {
                    None => {
                        in_states[target] = Some(state.clone());
                        worklist.push(target);
                    }
                    Some(existing) => {
                        let mut changed = false;
                        for (have, new) in existing.iter_mut().zip(&state) {
                            if *new == OWNED && *have != OWNED {
                                *have = OWNED;
                                changed = true;
                            }
                        }
                        if changed {
                            worklist.push(target);
                        }
                    }
                }
            };
            for inst in &self.blocks[block].insts {
                if let Inst::Call {
                    unwind: Some(target),
                    ..
                }
                | Inst::CallIndirect {
                    unwind: Some(target),
                    ..
                } = inst
                {
                    push(*target, &mut in_states, &mut worklist);
                }
            }
            match &self.blocks[block].term {
                Some(Term::Goto(target, _)) => push(*target, &mut in_states, &mut worklist),
                Some(Term::Branch {
                    then_block,
                    else_block,
                    ..
                }) => {
                    push(*then_block, &mut in_states, &mut worklist);
                    push(*else_block, &mut in_states, &mut worklist);
                }
                Some(Term::Switch {
                    targets, default, ..
                }) => {
                    for target in targets.iter().copied().chain(std::iter::once(*default)) {
                        push(target, &mut in_states, &mut worklist);
                    }
                }
                _ => {}
            }
        }

        // --- Realization: insert decided instructions, remap indices.
        self.apply_insertions(insertions, new_events, sites.event_seqs);
        // The drain surfaces the LAST pushed error; the walk's abort
        // semantics surfaced the FIRST violation, so push reversed.
        errors.sort_by_key(|(seq, _)| *seq);
        self.deferred_errors
            .extend(errors.into_iter().rev().map(|(_, error)| error));
    }

    fn apply_insertions(
        &mut self,
        mut insertions: Vec<Insertion>,
        new_events: Vec<(u32, FlowRecord)>,
        seqs: Vec<u32>,
    ) {
        // Splice the decided events into walk order: the planner and the
        // verifier replay same-index events in stream order, and a
        // decided Move/Use belongs exactly where the walk consumed.
        let mut merged: Vec<(u32, FlowRecord)> = self
            .flow_events
            .drain(..)
            .enumerate()
            .map(|(position, record)| (seqs.get(position).copied().unwrap_or(u32::MAX), record))
            .collect();
        merged.extend(new_events);
        merged.sort_by_key(|(seq, _)| *seq);
        self.flow_events = merged.into_iter().map(|(_, record)| record).collect();
        if insertions.is_empty() {
            return;
        }
        insertions.sort_by_key(|insertion| (insertion.block, insertion.index));
        let mut per_block: FxHashMap<BlockId, Vec<(u32, Vec<Inst>)>> = FxHashMap::default();
        for insertion in insertions {
            per_block
                .entry(insertion.block)
                .or_default()
                .push((insertion.index, insertion.insts));
        }
        for (block, mut inserts) in per_block {
            inserts.sort_by_key(|(index, _)| *index);
            // Rebuild the instruction list with insertions applied, and
            // compute the index shift table for event remapping.
            let old = std::mem::take(&mut self.blocks[block].insts);
            let mut shifted: Vec<u32> = Vec::with_capacity(old.len() + 1);
            let mut rebuilt: Vec<Inst> = Vec::with_capacity(old.len() + inserts.len());
            let mut cursor = 0usize;
            for (i, inst) in old.into_iter().enumerate() {
                while cursor < inserts.len() && inserts[cursor].0 as usize <= i {
                    for new_inst in std::mem::take(&mut inserts[cursor].1) {
                        rebuilt.push(new_inst);
                    }
                    cursor += 1;
                }
                shifted.push(rebuilt.len() as u32);
                rebuilt.push(inst);
            }
            while cursor < inserts.len() {
                for new_inst in std::mem::take(&mut inserts[cursor].1) {
                    rebuilt.push(new_inst);
                }
                cursor += 1;
            }
            shifted.push(rebuilt.len() as u32);
            // Debug provenance must stay aligned with instructions.
            let generated = self.generated_origin_debug();
            if let Some(debug) = &mut self.blocks[block].debug {
                let origins = std::mem::take(&mut debug.origins);
                let mut rebuilt_origins = Vec::with_capacity(rebuilt.len());
                let mut source = origins.into_iter();
                let mut next_shift = shifted.iter().copied().enumerate().peekable();
                let mut position = 0u32;
                for _ in 0..rebuilt.len() {
                    let is_original = next_shift
                        .peek()
                        .is_some_and(|(_, target)| *target == position);
                    if is_original {
                        next_shift.next();
                        rebuilt_origins.push(source.next().unwrap_or(generated));
                    } else {
                        rebuilt_origins.push(generated);
                    }
                    position += 1;
                }
                debug.origins = rebuilt_origins;
            }
            self.blocks[block].insts = rebuilt;
            for record in &mut self.flow_events {
                if record.block == block {
                    let old_index = record.index as usize;
                    record.index = *shifted
                        .get(old_index)
                        .unwrap_or_else(|| shifted.last().unwrap_or(&record.index));
                }
            }
        }
    }
}

/// Backward liveness over the recorded USE EVENTS (source-level reads,
/// consumes, loans) — not raw instruction operands: lowering
/// structurally re-reads consumed registers (match settling, repacks),
/// and those reads must not extend a value's source liveness. `Def`
/// events kill backward — a rebinding starts a new incarnation, so the
/// old value's liveness stops at the definition. Views fold into roots
/// at their use points. Computed per site during one backward CFG
/// fixpoint.
struct Liveness {
    /// Per consume-site seq: is the local live after the site?
    live_after: FxHashMap<u32, bool>,
    /// Per displace/writeback-site seq: is any view of the local live?
    view_live_at: FxHashMap<u32, bool>,
}

enum PointKind {
    Use(LocalId),
    Def(LocalId),
    /// A consume site: records live-after, then acts as a use.
    Consume(u32, LocalId),
    /// Displace/writeback: records whether any listed view is live.
    ViewQuery(u32, Vec<LocalId>),
}

impl Liveness {
    #[allow(clippy::too_many_arguments)]
    fn compute(
        blocks: &[super::BlockData],
        n_locals: usize,
        view_edges: &FxHashMap<LocalId, LocalId>,
        sites: &OwnershipSites,
        event_seqs: &[u32],
        flow_events: &[FlowRecord],
    ) -> Liveness {
        let words = n_locals.div_ceil(64).max(1);
        let mut views_of: FxHashMap<LocalId, Vec<LocalId>> = FxHashMap::default();
        for (view, root) in view_edges {
            views_of.entry(*root).or_default().push(*view);
        }

        // Build each block's point list in walk order (seq).
        let mut points: Vec<Vec<(u32, PointKind)>> = Vec::new();
        points.resize_with(blocks.len(), Vec::new);
        for read in &sites.reads {
            points[read.block].push((read.seq, PointKind::Use(read.local)));
        }
        for loan in &sites.loans {
            // Borrowing mentions the root (a source occurrence) and
            // BIRTHS the view: the view's liveness cannot extend above
            // its creation.
            points[loan.block].push((loan.seq, PointKind::Def(loan.view)));
            points[loan.block].push((loan.seq + 1, PointKind::Use(loan.root)));
        }
        let mut loan_views_of: FxHashMap<LocalId, Vec<LocalId>> = FxHashMap::default();
        for loan in &sites.loans {
            loan_views_of.entry(loan.root).or_default().push(loan.view);
        }
        for read in &sites.reads {
            if let Some(views) = loan_views_of.get(&read.local) {
                points[read.block].push((read.seq, PointKind::ViewQuery(read.seq, views.clone())));
            }
        }
        for site in &sites.sites {
            match site.kind {
                SiteKind::Consume { .. } => {
                    points[site.block].push((site.seq, PointKind::Consume(site.seq, site.local)));
                    if let Some(views) = loan_views_of.get(&site.local) {
                        points[site.block]
                            .push((site.seq, PointKind::ViewQuery(site.seq, views.clone())));
                    }
                }
                SiteKind::Displace | SiteKind::Writeback => {
                    let views = views_of.get(&site.local).cloned().unwrap_or_default();
                    points[site.block].push((site.seq, PointKind::ViewQuery(site.seq, views)));
                }
            }
        }
        for (position, record) in flow_events.iter().enumerate() {
            let seq = event_seqs.get(position).copied().unwrap_or(u32::MAX);
            if let FlowEvent::Def(local) = record.event {
                points[record.block].push((seq, PointKind::Def(local)));
            }
        }
        for bucket in &mut points {
            bucket.sort_by_key(|(seq, _)| *seq);
        }

        let set = |bits: &mut [u64], local: LocalId| {
            bits[usize::from(local) / 64] |= 1u64 << (usize::from(local) % 64)
        };
        let clear = |bits: &mut [u64], local: LocalId| {
            bits[usize::from(local) / 64] &= !(1u64 << (usize::from(local) % 64))
        };
        let get = |bits: &[u64], local: LocalId| {
            bits[usize::from(local) / 64] & (1u64 << (usize::from(local) % 64)) != 0
        };

        // Successor map (unwind edges included).
        let mut successors: Vec<Vec<BlockId>> = vec![Vec::new(); blocks.len()];
        for (id, block) in blocks.iter().enumerate() {
            for inst in &block.insts {
                if let Inst::Call {
                    unwind: Some(target),
                    ..
                }
                | Inst::CallIndirect {
                    unwind: Some(target),
                    ..
                } = inst
                {
                    successors[id].push(*target);
                }
            }
            match &block.term {
                Some(Term::Goto(target, _)) => successors[id].push(*target),
                Some(Term::Branch {
                    then_block,
                    else_block,
                    ..
                }) => successors[id].extend([*then_block, *else_block]),
                Some(Term::Switch {
                    targets, default, ..
                }) => {
                    successors[id].extend(targets.iter().copied());
                    successors[id].push(*default);
                }
                _ => {}
            }
        }

        let mut block_entry: Vec<Vec<u64>> = vec![vec![0; words]; blocks.len()];
        // (block_entry is the fixpoint state; per-site answers are what
        // the replay consumes.)
        let mut live_after: FxHashMap<u32, bool> = FxHashMap::default();
        let mut view_live_at: FxHashMap<u32, bool> = FxHashMap::default();
        let mut changed = true;
        while changed {
            changed = false;
            for (id, _) in blocks.iter().enumerate().rev() {
                // live-out = union of successors' entries.
                let mut live = vec![0u64; words];
                for target in &successors[id] {
                    or_into(&mut live, &block_entry[*target]);
                }
                // Apply this block's points in reverse walk order.
                for (seq, point) in points[id].iter().rev() {
                    match point {
                        PointKind::Def(local) => clear(&mut live, *local),
                        PointKind::Use(local) => {
                            set(&mut live, *local);
                            // A view use keeps its root's value pinned.
                            // (Roots fold in for donation decisions.)
                        }
                        PointKind::Consume(site_seq, local) => {
                            live_after.insert(*site_seq, get(&live, *local));
                            set(&mut live, *local);
                            let _ = seq;
                        }
                        PointKind::ViewQuery(site_seq, views) => {
                            view_live_at
                                .insert(*site_seq, views.iter().any(|view| get(&live, *view)));
                        }
                    }
                }
                if live != block_entry[id] {
                    block_entry[id] = live;
                    changed = true;
                }
            }
        }

        Liveness {
            live_after,
            view_live_at,
        }
    }

    fn after_site(&self, seq: u32) -> bool {
        self.live_after.get(&seq).copied().unwrap_or(false)
    }

    fn view_live_site(&self, seq: u32) -> bool {
        self.view_live_at.get(&seq).copied().unwrap_or(false)
    }
}

fn or_into(dest: &mut [u64], src: &[u64]) {
    for (d, s) in dest.iter_mut().zip(src) {
        *d |= *s;
    }
}
