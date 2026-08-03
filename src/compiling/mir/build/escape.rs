//! Which values stay inside their frame — MIR-owned facts (ADR 0044
//! rule 3, ADR 0045).
//!
//! A record, tuple, or enum payload is a value: nothing in MIR owns it,
//! and the backend picks its storage. The cheapest substrate is the
//! frame itself — one storage slot per construction site, reused on
//! every execution — and the conservative one is the arena, which is not
//! reclaimed until exit. The analysis here decides, per construction
//! site and per local, which substrate is sound, and `shape_frames`
//! publishes the answers on each `Function` so backends read them
//! instead of re-deriving them.
//!
//! The analysis is deliberately conservative: every use that could let a
//! value outlive the frame counts as an escape, including flow into a
//! block parameter, which is what keeps a site's single storage slot
//! from being observed across a loop's back edge.

use rustc_hash::{FxHashMap, FxHashSet};

use super::{Escape, Function, Inst, LocalId, Operand, Program, Slot, Term, visit_inst, visit_term};

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

/// One function's frame-local construction sites, as `(block,
/// instruction)`: the sites whose value provably stays in this frame.
/// Read from the register-allocated function. Slot reuse can only make
/// this more conservative: a slot shared with an escaping value is
/// treated as escaping.
fn frame_sites(
    function: &Function,
    summaries: &[Vec<bool>],
) -> std::collections::HashSet<(usize, usize)> {
    let mut sites = std::collections::HashSet::default();
    let escaping = escaping_locals(function, summaries);
    for (block_index, block) in function.blocks.iter().enumerate() {
        for (instruction_index, inst) in block.insts.iter().enumerate() {
            let dest = match inst {
                Inst::Aggregate { dest, .. } => *dest,
                _ => continue,
            };
            if !escaping.contains(&dest) {
                sites.insert((block_index, instruction_index));
            }
        }
    }
    sites
}

/// Which locals may reabstract into reusable frame storage: those whose
/// value originates only at frame-local construction sites, followed
/// through copies and block-parameter edges. A value that arrives from
/// outside every judged site — a parameter, a call result, any other
/// definition — must use the arena: nothing proved its box may die with
/// this frame (a `next`-style callee returning its evolved parameter
/// inside the writeback tuple would otherwise hand its caller a pointer
/// into a dead frame).
fn frame_local_values(
    function: &Function,
    sites: &std::collections::HashSet<(usize, usize)>,
) -> Vec<bool> {
    enum Origin {
        Site(u16, bool),
        From(u16, u16),
    }
    let mut origins = Vec::new();
    for local in 0..function.arity {
        origins.push(Origin::Site(local, false));
    }
    for (block_index, block) in function.blocks.iter().enumerate() {
        for (instruction_index, inst) in block.insts.iter().enumerate() {
            match inst {
                Inst::Aggregate { dest, .. } => {
                    origins.push(Origin::Site(
                        *dest,
                        sites.contains(&(block_index, instruction_index)),
                    ));
                }
                Inst::Copy {
                    dest,
                    src: Operand::Local(src),
                } => origins.push(Origin::From(*dest, *src)),
                other => {
                    let mut probe = other.clone();
                    super::visit_inst(&mut probe, &mut |slot, local| {
                        if slot == super::Slot::Def {
                            origins.push(Origin::Site(*local, false));
                        }
                    });
                }
            }
        }
        if let Some(Term::Goto(target, args)) = &block.term {
            for (param, arg) in function.blocks[*target].params.iter().zip(args) {
                match arg {
                    Operand::Local(src) => origins.push(Origin::From(*param, *src)),
                    Operand::Const(_) => origins.push(Origin::Site(*param, false)),
                }
            }
        }
    }
    let mut safe = vec![true; usize::from(function.n_locals())];
    loop {
        let mut changed = false;
        for origin in &origins {
            let (local, incoming) = match origin {
                Origin::Site(local, site_safe) => (*local, *site_safe),
                Origin::From(local, src) => (*local, safe[usize::from(*src)]),
            };
            if !incoming && safe[usize::from(local)] {
                safe[usize::from(local)] = false;
                changed = true;
            }
        }
        if !changed {
            return safe;
        }
    }
}

/// Stamp every function's published frame facts (ADR 0045): each
/// local's layout class and frame-locality, and each construction
/// site's substrate. Runs after register allocation, on the numbering
/// the backends will see; `summaries` comes from before it.
pub(crate) fn shape_frames(program: &mut Program, summaries: &[Vec<bool>]) {
    // Layout classes arrive already stamped on `function.locals` by
    // register allocation (the one derivation point); this pass adds
    // only the escape-derived facts.
    for function in program.functions.iter_mut() {
        let sites = frame_sites(function, summaries);
        let frame_local = frame_local_values(function, &sites);
        for (local, info) in function.locals.iter_mut().enumerate() {
            info.frame_local = frame_local.get(local).copied().unwrap_or(false);
        }
        function.frame_sites = sites;
    }
}

/// Locals whose value may outlive the frame. A `Copy` propagates
/// backwards: if the destination escapes, so does everything copied into
/// it.
fn escaping_locals(function: &Function, summaries: &[Vec<bool>]) -> FxHashSet<LocalId> {
    let mut escaping = FxHashSet::default();
    let mut copied_into: FxHashMap<LocalId, Vec<LocalId>> = FxHashMap::default();
    let sink = |slot: Slot, local: &mut LocalId, escaping: &mut FxHashSet<LocalId>| {
        if matches!(slot, Slot::Use(Escape::May)) {
            escaping.insert(*local);
        }
    };

    for block in &function.blocks {
        for inst in &block.insts {
            match inst {
                // A `Copy` propagates backwards instead of escaping: if
                // the destination escapes, so does the source.
                Inst::Copy {
                    dest,
                    src: Operand::Local(src),
                } => copied_into.entry(*dest).or_default().push(*src),
                Inst::Copy { .. } => {}
                // A direct call escapes an argument only when the callee
                // lets that parameter outlive it — the one use the
                // visitor's static classification cannot refine.
                Inst::Call { func, args, .. } => {
                    for (index, arg) in args.iter().enumerate() {
                        let escapes = summaries
                            .get(*func)
                            .and_then(|summary| summary.get(index))
                            .copied()
                            .unwrap_or(true);
                        if escapes && let Operand::Local(local) = arg {
                            escaping.insert(*local);
                        }
                    }
                }
                other => {
                    let mut probe = other.clone();
                    visit_inst(&mut probe, &mut |slot, local| {
                        sink(slot, local, &mut escaping);
                    });
                }
            }
        }
        if let Some(term) = &block.term {
            let mut probe = term.clone();
            visit_term(&mut probe, &mut |slot, local| {
                sink(slot, local, &mut escaping);
            });
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
