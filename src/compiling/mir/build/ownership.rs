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
    contains_object, contains_source_deinit, donates, is_linear, needs_drop,
};
use crate::compiling::mir::cfg::{Cfg, bits};
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
    pub index: u32,
    pub root: LocalId,
    pub view: LocalId,
    pub view_name: String,
    pub exclusive: bool,
}

#[derive(Clone, Debug)]
pub(super) struct ProjectionSite {
    pub block: BlockId,
    pub seq: u32,
    pub index: u32,
    pub owner: LocalId,
    pub projection: LocalId,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Default)]
pub(super) struct OwnershipSites {
    pub sites: Vec<OwnershipSite>,
    pub reads: Vec<ReadSite>,
    pub loans: Vec<LoanSite>,
    pub projections: Vec<ProjectionSite>,
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
                        callee: Operand::Borrow(witness),
                        args: vec![Operand::Borrow(payload)],
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
                    callee: Operand::Borrow(retain_witness),
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
        let value = Operand::Borrow(local);
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
                            callee: Operand::Borrow(witness),
                            args: vec![Operand::Borrow(payload)],
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
                        callee: Operand::Borrow(drop_witness),
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
        let mut sites = std::mem::take(&mut self.ownership_sites);
        if sites.sites.is_empty()
            && sites.reads.is_empty()
            && sites.loans.is_empty()
            && sites.projections.is_empty()
        {
            return;
        }
        for projection in &sites.projections {
            sites.event_seqs.push(projection.seq);
            self.flow_events.push(FlowRecord {
                block: projection.block,
                index: projection.index,
                event: FlowEvent::Def(projection.projection),
            });
        }
        let n_locals = self.locals_len();
        let cfg = Cfg::new(&self.blocks);
        let live = Liveness::compute(
            &cfg,
            &self.blocks,
            n_locals,
            &self.view_edges(),
            &self.borrow_roots,
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
        for projection in &sites.projections {
            match self.realize_retain(
                Operand::Borrow(projection.projection),
                &projection.ty,
                projection.span,
            ) {
                Ok(insts) => insertions.push(Insertion {
                    block: projection.block,
                    index: projection.index,
                    insts,
                }),
                Err(error) => errors.push((projection.seq, error)),
            }
        }
        let mut drop_points: Vec<Vec<DropPoint>> =
            (0..self.blocks.len()).map(|_| Vec::new()).collect();
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
        let settled_projections: FxHashSet<LocalId> = sites
            .projections
            .iter()
            .map(|projection| projection.projection)
            .collect();
        let mut deferred_to_join: FxHashSet<LocalId> = self
            .init_field_shadows
            .values()
            .map(|(local, _)| *local)
            .collect();
        deferred_to_join.extend(
            self.borrow_roots
                .keys()
                .copied()
                .filter(|local| !settled_projections.contains(local)),
        );

        while let Some(block) = worklist.pop() {
            let Some(mut state) = in_states[block].clone() else {
                continue;
            };
            let mut cursor = 0usize;
            let mut placed = Vec::new();
            let end = self.blocks[block].insts.len() as u32;
            let trap = matches!(self.blocks[block].term, Some(Term::Trap(_)));
            for point in 0..=end {
                while cursor < agenda[block].len() && agenda[block][cursor].0.0 <= point {
                    let ((index, entry_seq), entry) = &agenda[block][cursor];
                    cursor += 1;
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
                            if !owned && self.tracks(read.local) && reported.insert((block, *index))
                            {
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
                                                Operand::Borrow(site.local),
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
                                                    src: Operand::Borrow(site.local),
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
                                            match self.realize_drop(site.local, &site.ty, site.span)
                                            {
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
                                            Operand::Borrow(site.local),
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
                                            src: Operand::Borrow(site.local),
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
                if trap {
                    continue;
                }
                let mut released = Vec::new();
                for local in (0..state.len()).rev() {
                    let local = local as LocalId;
                    if state[usize::from(local)] == OWNED
                        && self
                            .frame
                            .get(usize::from(local))
                            .and_then(|entry| entry.declared.as_ref())
                            .is_some_and(|ty| contains_source_deinit(self.program_builder, ty))
                        && !deferred_to_join.contains(&local)
                        && !live.any_live_at(block, point, local)
                    {
                        state[usize::from(local)] = 0;
                        released.push(local);
                    }
                }
                if !released.is_empty() {
                    placed.push(DropPoint {
                        block,
                        index: point,
                        locals: released,
                    });
                }
            }
            drop_points[block] = placed;

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
                            if *have == *new || *have == super::verify::CONFLICT {
                                continue;
                            }
                            if *have == OWNED || *new == OWNED || *new == super::verify::CONFLICT {
                                *have = super::verify::CONFLICT;
                                changed = true;
                            }
                        }
                        if changed {
                            worklist.push(target);
                        }
                    }
                }
            };
            for target in &cfg.successors[block] {
                push(*target, &mut in_states, &mut worklist);
            }
        }

        // --- Realization: insert decided instructions, remap indices, then
        // split blocks at first-dead points and emit their structural drops.
        let mut drops: Vec<DropPoint> = drop_points.into_iter().flatten().collect();
        self.apply_insertions(insertions, new_events, sites.event_seqs, &mut drops);
        self.realize_placement(drops);
        // The drain surfaces the LAST pushed error; the walk's abort
        // semantics surfaced the FIRST violation, so push reversed.
        errors.sort_by_key(|(seq, _)| *seq);
        self.deferred_errors
            .extend(errors.into_iter().rev().map(|(_, error)| error));
    }

    fn realize_placement(&mut self, drops: Vec<DropPoint>) {
        let mut by_block: FxHashMap<BlockId, Vec<DropPoint>> = FxHashMap::default();
        for drop in drops {
            by_block.entry(drop.block).or_default().push(drop);
        }
        let mut blocks: Vec<BlockId> = by_block.keys().copied().collect();
        blocks.sort_unstable();
        for block in blocks {
            let mut points = by_block.remove(&block).unwrap_or_default();
            points.sort_by_key(|point| std::cmp::Reverse(point.index));
            for point in points {
                let continuation = self.split_block(block, point.index);
                self.switch_to(block);
                for local in point.locals {
                    self.generated_origin = self.cleanup_origin(super::CleanupKind::LastUse, local);
                    self.release_planned(local);
                }
                self.terminate(Term::Goto(continuation, Vec::new()));
            }
        }
    }

    fn split_block(&mut self, block: BlockId, index: u32) -> BlockId {
        let continuation = self.new_block();
        let at = index as usize;
        let data = &mut self.blocks[block];
        let tail: Vec<Inst> = data.insts.drain(at..).collect();
        let term = data.term.take();
        let origins = data.debug.as_mut().map(|debug| {
            debug
                .origins
                .drain(at.min(debug.origins.len())..)
                .collect::<Vec<_>>()
        });
        let continuation_data = &mut self.blocks[continuation];
        continuation_data.insts = tail;
        continuation_data.term = term;
        if let (Some(debug), Some(origins)) = (continuation_data.debug.as_mut(), origins) {
            debug.origins = origins;
        }
        for record in &mut self.flow_events {
            if record.block == block && record.index > index {
                record.block = continuation;
                record.index -= index;
            }
        }
        continuation
    }

    fn apply_insertions(
        &mut self,
        mut insertions: Vec<Insertion>,
        new_events: Vec<(u32, FlowRecord)>,
        seqs: Vec<u32>,
        drops: &mut [DropPoint],
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
            for point in drops.iter_mut() {
                if point.block == block {
                    let old_index = point.index as usize;
                    point.index = *shifted
                        .get(old_index)
                        .unwrap_or_else(|| shifted.last().unwrap_or(&point.index));
                }
            }
        }
    }
}

struct DropPoint {
    block: BlockId,
    index: u32,
    locals: Vec<LocalId>,
}

/// One backward CFG fixpoint with two facets. Source liveness decides
/// donate versus move and borrow exclusivity. Any-use liveness places a
/// release at the first point where an owned value and every managed view of
/// it are dead.
struct Liveness {
    words: usize,
    any_at: Vec<Vec<Vec<u64>>>,
    live_after: FxHashMap<u32, bool>,
    view_live_at: FxHashMap<u32, bool>,
}

enum PointKind {
    Inst(u32),
    Use(LocalId),
    Def(LocalId),
    Consume(u32, LocalId),
    ViewQuery(u32, Vec<LocalId>),
    Settled(LocalId),
}

impl Liveness {
    #[allow(clippy::too_many_arguments)]
    fn compute(
        cfg: &Cfg,
        blocks: &[super::BlockData],
        n_locals: usize,
        view_edges: &FxHashMap<LocalId, LocalId>,
        projection_roots: &FxHashMap<LocalId, LocalId>,
        sites: &OwnershipSites,
        event_seqs: &[u32],
        flow_events: &[FlowRecord],
    ) -> Liveness {
        let words = n_locals.div_ceil(64).max(1);
        let tracked: FxHashSet<LocalId> = flow_events
            .iter()
            .filter_map(|record| match record.event {
                FlowEvent::Def(local)
                | FlowEvent::Use(local)
                | FlowEvent::Move(local)
                | FlowEvent::Drop(local) => Some(local),
                _ => None,
            })
            .collect();
        let writeback_slots: FxHashSet<LocalId> = sites
            .sites
            .iter()
            .filter_map(|site| matches!(site.kind, SiteKind::Writeback).then_some(site.local))
            .collect();
        let mut views_of: FxHashMap<LocalId, Vec<LocalId>> = FxHashMap::default();
        for (view, root) in view_edges {
            views_of.entry(*root).or_default().push(*view);
        }
        let mut roots = projection_roots.clone();
        let mut changed = true;
        while changed {
            changed = false;
            let required: FxHashSet<LocalId> = roots.values().copied().collect();
            for block in blocks {
                for inst in &block.insts {
                    let Inst::Copy {
                        dest,
                        src: Operand::Borrow(source),
                    } = inst
                    else {
                        continue;
                    };
                    if !required.contains(dest) || roots.contains_key(dest) {
                        continue;
                    }
                    if let Some(root) = roots.get(source).copied() {
                        roots.insert(*dest, root);
                        changed = true;
                    }
                }
            }
        }
        let mut kept_alive: FxHashMap<LocalId, Vec<LocalId>> = FxHashMap::default();
        for (view, root) in view_edges {
            kept_alive.entry(*view).or_default().push(*root);
        }
        for (local, root) in &roots {
            if !tracked.contains(local) && local != root {
                let roots = kept_alive.entry(*local).or_default();
                if !roots.contains(root) {
                    roots.push(*root);
                }
            }
        }

        let mut points: Vec<Vec<((u32, u32, u8), PointKind)>> =
            (0..blocks.len()).map(|_| Vec::new()).collect();
        for read in &sites.reads {
            points[read.block].push(((read.index, read.seq, 1), PointKind::Use(read.local)));
        }
        for loan in &sites.loans {
            points[loan.block].push(((loan.index, loan.seq, 0), PointKind::Def(loan.view)));
            points[loan.block].push(((loan.index, loan.seq, 1), PointKind::Use(loan.root)));
        }
        let mut loan_views_of: FxHashMap<LocalId, Vec<LocalId>> = FxHashMap::default();
        for loan in &sites.loans {
            loan_views_of.entry(loan.root).or_default().push(loan.view);
        }
        for read in &sites.reads {
            if let Some(views) = loan_views_of.get(&read.local) {
                points[read.block].push((
                    (read.index, read.seq, 0),
                    PointKind::ViewQuery(read.seq, views.clone()),
                ));
            }
        }
        for site in &sites.sites {
            match site.kind {
                SiteKind::Consume { .. } => {
                    points[site.block].push((
                        (site.index, site.seq, 1),
                        PointKind::Consume(site.seq, site.local),
                    ));
                    if let Some(views) = loan_views_of.get(&site.local) {
                        points[site.block].push((
                            (site.index, site.seq, 0),
                            PointKind::ViewQuery(site.seq, views.clone()),
                        ));
                    }
                }
                SiteKind::Displace | SiteKind::Writeback => {
                    let views = views_of.get(&site.local).cloned().unwrap_or_default();
                    points[site.block].push((
                        (site.index, site.seq, 0),
                        PointKind::ViewQuery(site.seq, views),
                    ));
                }
            }
        }
        for (position, record) in flow_events.iter().enumerate() {
            let seq = event_seqs.get(position).copied().unwrap_or(u32::MAX);
            if let FlowEvent::Def(local) = record.event {
                points[record.block].push(((record.index, seq, 1), PointKind::Def(local)));
            }
        }
        for projection in &sites.projections {
            points[projection.block].push((
                (projection.index, projection.seq, 0),
                PointKind::Settled(projection.owner),
            ));
        }

        let mut operands: Vec<Vec<(Vec<LocalId>, Vec<LocalId>)>> = Vec::new();
        for (block, data) in blocks.iter().enumerate() {
            let mut block_operands = Vec::new();
            for (index, inst) in data.insts.iter().enumerate() {
                points[block].push(((index as u32, u32::MAX, 2), PointKind::Inst(index as u32)));
                let mut probe = inst.clone();
                let mut defs = Vec::new();
                let mut uses = Vec::new();
                super::visit_inst(&mut probe, &mut |slot, local| match slot {
                    super::Slot::Def => defs.push(*local),
                    super::Slot::Use(_) => uses.push(*local),
                });
                block_operands.push((defs, uses));
            }
            points[block].sort_by_key(|(position, _)| *position);
            operands.push(block_operands);
        }

        let term_uses: Vec<Vec<LocalId>> = blocks
            .iter()
            .map(|block| {
                let mut uses = Vec::new();
                if let Some(term) = &block.term {
                    let mut probe = term.clone();
                    super::visit_term(&mut probe, &mut |slot, local| {
                        if slot.is_use() {
                            uses.push(*local);
                        }
                    });
                }
                uses
            })
            .collect();

        let ordered: Vec<Vec<PointKind>> = points
            .into_iter()
            .map(|points| points.into_iter().map(|(_, point)| point).collect())
            .collect();
        let mut any_at: Vec<Vec<Vec<u64>>> = blocks
            .iter()
            .map(|block| vec![Vec::new(); block.insts.len() + 1])
            .collect();
        let mut live_after = FxHashMap::default();
        let mut view_live_at = FxHashMap::default();

        cfg.backward_bits(words * 2, |block, live| {
            let (any, source) = live.split_at_mut(words);
            for local in &term_uses[block] {
                Self::use_with_roots(any, *local, &kept_alive, n_locals);
            }
            any_at[block][blocks[block].insts.len()] = any.to_vec();
            for point in ordered[block].iter().rev() {
                match point {
                    PointKind::Inst(index) => {
                        let (defs, uses) = &operands[block][*index as usize];
                        for local in defs {
                            if usize::from(*local) < n_locals {
                                // Tracked mutable slots publish replacement through
                                // ownership sites; clearing them here would make the old
                                // and writeback incarnations look like a gap.
                                if !writeback_slots.contains(local) {
                                    bits::clear(any, *local);
                                }
                                if view_edges.contains_key(local) {
                                    bits::clear(source, *local);
                                }
                            }
                        }
                        for local in uses {
                            Self::use_with_roots(any, *local, &kept_alive, n_locals);
                        }
                        any_at[block][*index as usize] = any.to_vec();
                    }
                    PointKind::Use(local) => {
                        Self::use_with_roots(any, *local, &kept_alive, n_locals);
                        if usize::from(*local) < n_locals {
                            bits::set(source, *local);
                        }
                    }
                    PointKind::Def(local) => {
                        if usize::from(*local) < n_locals {
                            bits::clear(source, *local);
                        }
                    }
                    PointKind::Consume(seq, local) => {
                        live_after.insert(
                            *seq,
                            usize::from(*local) < n_locals && bits::get(source, *local),
                        );
                        Self::use_with_roots(any, *local, &kept_alive, n_locals);
                        if usize::from(*local) < n_locals {
                            bits::set(source, *local);
                        }
                    }
                    PointKind::ViewQuery(seq, views) => {
                        view_live_at.insert(
                            *seq,
                            views.iter().any(|view| {
                                usize::from(*view) < n_locals && bits::get(source, *view)
                            }),
                        );
                    }
                    PointKind::Settled(local) => {
                        Self::use_with_roots(any, *local, &kept_alive, n_locals);
                    }
                }
            }
            for param in &blocks[block].params {
                if usize::from(*param) < n_locals {
                    bits::clear(any, *param);
                    bits::clear(source, *param);
                }
            }
        });

        Liveness {
            words,
            any_at,
            live_after,
            view_live_at,
        }
    }

    fn use_with_roots(
        live: &mut [u64],
        local: LocalId,
        kept_alive: &FxHashMap<LocalId, Vec<LocalId>>,
        n_locals: usize,
    ) {
        let mut pending = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(current) = pending.pop() {
            if !seen.insert(current) {
                continue;
            }
            if usize::from(current) < n_locals {
                bits::set(live, current);
            }
            if let Some(roots) = kept_alive.get(&current) {
                pending.extend(roots.iter().copied());
            }
        }
    }

    fn after_site(&self, seq: u32) -> bool {
        self.live_after.get(&seq).copied().unwrap_or(false)
    }

    fn view_live_site(&self, seq: u32) -> bool {
        self.view_live_at.get(&seq).copied().unwrap_or(false)
    }

    fn any_live_at(&self, block: BlockId, point: u32, local: LocalId) -> bool {
        let Some(set) = self
            .any_at
            .get(block)
            .and_then(|points| points.get(point as usize))
        else {
            return false;
        };
        set.len() == self.words && usize::from(local) < self.words * 64 && bits::get(set, local)
    }
}
