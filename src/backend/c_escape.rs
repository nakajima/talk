//! Which aggregate construction sites can live in the frame.
//!
//! A record, tuple, or enum payload is a value: nothing in MIR owns it,
//! and the backend picks its storage. The C backend's default is a bump
//! arena that is not reclaimed until exit, which for an allocation-heavy
//! loop means page faults dominate — measured on `bench/fields.tlk` at
//! three million iterations, kernel time exceeded user time.
//!
//! A construction whose value never leaves the frame does not need the
//! arena at all: it can live in the activation, one storage slot per
//! site, reused on every execution of that site. That is ADR 0044's rule
//! 3 — start at the cheapest substrate, latch toward the conservative one
//! when an owning sink is observed — applied to value aggregates, and it
//! is the analysis the ADR says MIR should eventually own rather than a
//! backend.
//!
//! The analysis is deliberately conservative: every use that could let a
//! value outlive the frame counts as an escape, including flow into a
//! block parameter, which is what keeps a site's single storage slot
//! from being observed across a loop's back edge.

use rustc_hash::{FxHashMap, FxHashSet};

use super::mir::{Function, Inst, LocalId, Operand, Program, Term};

/// The construction sites, as `(function, block, instruction)`, whose
/// value provably stays in its frame.
pub(crate) type FrameSites = FxHashSet<(usize, usize, usize)>;

/// Whether each function lets each parameter outlive the call.
///
/// Computed on the program *before* register allocation, where every
/// local has a single definition. After `reuse_locals` a parameter's slot
/// can be recycled for an unrelated temporary, and one that happens to be
/// returned would make the parameter look escaping — which costs every
/// caller its frame allocation. This is a property of what the callee
/// does, not of how its registers were assigned, so the earlier program
/// is the right place to read it.
pub(crate) fn parameter_summaries(program: &Program) -> Vec<Vec<bool>> {
    summaries(program)
}

/// The sites, read from the register-allocated program the emitter will
/// walk. Slot reuse can only make this more conservative: a slot shared
/// with an escaping value is treated as escaping.
pub(crate) fn frame_sites(program: &Program, escaping_parameters: &[Vec<bool>]) -> FrameSites {
    let mut sites = FrameSites::default();
    let debug = std::env::var_os("TALK_C_ESCAPE_DEBUG").is_some();
    for (id, function) in program.functions.iter().enumerate() {
        let escaping = escaping_locals(function, escaping_parameters);
        if debug {
            let mut sorted: Vec<_> = escaping.iter().copied().collect();
            sorted.sort_unstable();
            eprintln!(
                "fn{id} {} params={:?} escaping={sorted:?}",
                function.name, escaping_parameters[id]
            );
        }
        for (block_index, block) in function.blocks.iter().enumerate() {
            for (instruction_index, inst) in block.insts.iter().enumerate() {
                let dest = match inst {
                    Inst::Record { dest, .. }
                    | Inst::Tuple { dest, .. }
                    | Inst::Variant { dest, .. } => *dest,
                    _ => continue,
                };
                if !escaping.contains(&dest) {
                    sites.insert((id, block_index, instruction_index));
                }
            }
        }
    }
    sites
}

/// For each function, which parameters can outlive the call. Computed to
/// a fixpoint from the optimistic assumption that none can, so a cycle of
/// mutually recursive functions settles on "escapes" only when some
/// concrete use forces it.
fn summaries(program: &Program) -> Vec<Vec<bool>> {
    let mut summaries: Vec<Vec<bool>> = program
        .functions
        .iter()
        .map(|function| vec![false; function.arity as usize])
        .collect();
    loop {
        let mut changed = false;
        for (id, function) in program.functions.iter().enumerate() {
            let escaping = escaping_locals(function, &summaries);
            for parameter in 0..function.arity {
                // Parameters occupy the first locals of the frame.
                if escaping.contains(&parameter) && !summaries[id][parameter as usize] {
                    summaries[id][parameter as usize] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            return summaries;
        }
    }
}

/// Locals whose value may outlive the frame. A `Copy` propagates
/// backwards: if the destination escapes, so does everything copied into
/// it.
fn escaping_locals(function: &Function, summaries: &[Vec<bool>]) -> FxHashSet<LocalId> {
    let mut escaping = FxHashSet::default();
    let mut copied_into: FxHashMap<LocalId, Vec<LocalId>> = FxHashMap::default();
    let escape = |operand: &Operand, escaping: &mut FxHashSet<LocalId>| {
        if let Operand::Local(local) = operand {
            escaping.insert(*local);
        }
    };

    for block in &function.blocks {
        for inst in &block.insts {
            match inst {
                Inst::Copy {
                    dest,
                    src: Operand::Local(src),
                } => copied_into.entry(*dest).or_default().push(*src),
                Inst::Copy { .. } => {}

                // Reads. The aggregate itself stays where it is.
                Inst::GetField { .. }
                | Inst::GetPayload { .. }
                | Inst::GetTag { .. }
                | Inst::TupleGet { .. }
                | Inst::GetElement { .. }
                | Inst::IsUnique { .. }
                | Inst::ObjectGet { .. }
                | Inst::ExistentialWitness { .. }
                | Inst::ExistentialPayload { .. }
                | Inst::Scalar { .. }
                | Inst::EnvGet { .. }
                | Inst::MakeCont { .. }
                | Inst::GetFloor { .. }
                | Inst::GlobalLoad { .. }
                | Inst::Load { .. }
                | Inst::StringLit { .. }
                | Inst::BytesLit { .. }
                | Inst::CellGet { .. } => {}

                // A direct call escapes an argument only when the callee
                // lets that parameter outlive it.
                Inst::Call { func, args, .. } => {
                    for (index, arg) in args.iter().enumerate() {
                        let escapes = summaries
                            .get(*func)
                            .and_then(|summary| summary.get(index))
                            .copied()
                            .unwrap_or(true);
                        if escapes {
                            escape(arg, &mut escaping);
                        }
                    }
                }
                // The target is not known here, so everything escapes.
                Inst::CallIndirect { callee, args, .. } => {
                    escape(callee, &mut escaping);
                    for arg in args {
                        escape(arg, &mut escaping);
                    }
                }

                // Stores into anything that outlives the construction,
                // and every other sink.
                Inst::Record { args, .. }
                | Inst::Tuple { args, .. }
                | Inst::Variant { args, .. }
                | Inst::ObjectNew { args, .. }
                | Inst::MakeClosure { env: args, .. } => {
                    for arg in args {
                        escape(arg, &mut escaping);
                    }
                }
                Inst::ExistentialPack {
                    payload, witnesses, ..
                } => {
                    escape(payload, &mut escaping);
                    for witness in witnesses {
                        escape(witness, &mut escaping);
                    }
                }
                Inst::SetField { src, .. }
                | Inst::ObjectSet { src, .. }
                | Inst::CellNew { init: src, .. }
                | Inst::CellSet { src, .. }
                | Inst::GlobalStore { src, .. }
                | Inst::RegionAcquire { src }
                | Inst::RegionRelease { src }
                | Inst::Free { src }
                | Inst::RetainPtr { src }
                | Inst::SetFloor { src } => escape(src, &mut escaping),
                Inst::Store { ptr, src, .. } => {
                    escape(ptr, &mut escaping);
                    escape(src, &mut escaping);
                }
                Inst::SetFinalizer { obj, closure } => {
                    escape(obj, &mut escaping);
                    escape(closure, &mut escaping);
                }
                Inst::PushHandler { clause, cont, .. } => {
                    escape(clause, &mut escaping);
                    escape(cont, &mut escaping);
                }
                Inst::AbortTo { cont, value } => {
                    escape(cont, &mut escaping);
                    escape(value, &mut escaping);
                }
                Inst::Alloc { bytes, .. } => escape(bytes, &mut escaping),
                Inst::PtrAdd { ptr, offset, .. } => {
                    escape(ptr, &mut escaping);
                    escape(offset, &mut escaping);
                }
                Inst::MemCopy { from, to, len } => {
                    escape(from, &mut escaping);
                    escape(to, &mut escaping);
                    escape(len, &mut escaping);
                }
                Inst::Io { a, b, c, .. } => {
                    escape(a, &mut escaping);
                    escape(b, &mut escaping);
                    escape(c, &mut escaping);
                }
                Inst::FindHandler { .. } => {}
            }
        }
        match &block.term {
            // Returning hands the value to a frame that outlives this
            // one; a block argument can carry it across a back edge,
            // where the site's single storage slot would be reused.
            Some(Term::Return(value)) => escape(value, &mut escaping),
            Some(Term::Goto(_, args)) => {
                for arg in args {
                    escape(arg, &mut escaping);
                }
            }
            Some(Term::Branch { .. } | Term::Switch { .. } | Term::Trap(_) | Term::UnwindRet)
            | None => {}
        }
    }

    // Propagate backwards through copies until stable.
    loop {
        let mut changed = false;
        for (dest, sources) in &copied_into {
            if !escaping.contains(dest) {
                continue;
            }
            for source in sources {
                changed |= escaping.insert(*source);
            }
        }
        if !changed {
            return escaping;
        }
    }
}
