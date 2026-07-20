//! Register reuse for lowered frames.
//!
//! The instruction builder allocates one frame local per binding and
//! per expression temporary and never recycles an index, so a large
//! function's frame grows with its length (tens of thousands of
//! registers), and every call pays an allocation, a fill, and a drop
//! proportional to that width. This pass renumbers a function's locals
//! onto the smallest set of registers whose live ranges never overlap:
//! liveness by iterative backward dataflow over the block graph (the
//! standard equations — Aho, Sethi & Ullman, *Compilers*, 1986, §10.6),
//! then interval assignment in linear order with a free list — linear
//! scan without spilling, since registers are unbounded (Poletto &
//! Sarkar, TOPLAS 1999).
//!
//! Parameters stay pinned at registers `0..arity`: the calling
//! convention writes arguments and mut-parameter writebacks there.
//! Unwind cleanup blocks are graph successors of the blocks that call
//! into them, so values read only during cleanup stay live across the
//! suspendable call.

use rustc_hash::FxHashMap;

use super::mir::{BlockData, Function, Inst, LocalId, Operand, Term};

/// Which side of an instruction a local appears on.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Slot {
    Def,
    Use,
}

/// Visit every local in an instruction, mutably: the one walk both the
/// analysis (read) and the rewrite (write) share, so an instruction
/// added with a new operand shape fails here once, not twice.
pub(crate) fn visit_inst(inst: &mut Inst, visit: &mut impl FnMut(Slot, &mut LocalId)) {
    let operand = |op: &mut Operand, visit: &mut dyn FnMut(Slot, &mut LocalId)| {
        if let Operand::Local(local) = op {
            visit(Slot::Use, local);
        }
    };
    match inst {
        Inst::Copy { dest, src }
        | Inst::TupleGet { dest, src, .. }
        | Inst::GetTag { dest, src }
        | Inst::GetPayload { dest, src, .. }
        | Inst::GetField { dest, src, .. }
        | Inst::IsUnique { dest, src }
        | Inst::ObjectGet { dest, src, .. }
        | Inst::ExistentialWitness { dest, src, .. }
        | Inst::ExistentialPayload { dest, src } => {
            operand(src, visit);
            visit(Slot::Def, dest);
        }
        Inst::GetElement { dest, src, index } => {
            operand(src, visit);
            operand(index, visit);
            visit(Slot::Def, dest);
        }
        Inst::Scalar { dest, a, b, .. } => {
            operand(a, visit);
            if let Some(b) = b {
                operand(b, visit);
            }
            visit(Slot::Def, dest);
        }
        Inst::Call { dest, args, .. }
        | Inst::Tuple { dest, args }
        | Inst::Variant { dest, args, .. }
        | Inst::Record { dest, args, .. }
        | Inst::ObjectNew { dest, args } => {
            for arg in args {
                operand(arg, visit);
            }
            visit(Slot::Def, dest);
        }
        Inst::CallIndirect {
            dest, callee, args, ..
        } => {
            operand(callee, visit);
            for arg in args {
                operand(arg, visit);
            }
            visit(Slot::Def, dest);
        }
        Inst::SetField { rec, src, .. } => {
            visit(Slot::Use, rec);
            operand(src, visit);
        }
        Inst::StringLit { dest, .. }
        | Inst::BytesLit { dest, .. }
        | Inst::EnvGet { dest, .. }
        | Inst::MakeCont { dest }
        | Inst::GetFloor { dest }
        | Inst::GlobalLoad { dest, .. } => visit(Slot::Def, dest),
        Inst::Alloc { dest, bytes } => {
            operand(bytes, visit);
            visit(Slot::Def, dest);
        }
        Inst::Free { src }
        | Inst::RetainPtr { src }
        | Inst::RegionAcquire { src }
        | Inst::RegionRelease { src }
        | Inst::SetFloor { src } => operand(src, visit),
        Inst::Load { dest, ptr, .. } => {
            operand(ptr, visit);
            visit(Slot::Def, dest);
        }
        Inst::Store { ptr, src, .. } => {
            operand(ptr, visit);
            operand(src, visit);
        }
        Inst::MemCopy { from, to, len } => {
            operand(from, visit);
            operand(to, visit);
            operand(len, visit);
        }
        Inst::PtrAdd {
            dest, ptr, offset, ..
        } => {
            operand(ptr, visit);
            operand(offset, visit);
            visit(Slot::Def, dest);
        }
        Inst::Io { dest, a, b, c, .. } => {
            operand(a, visit);
            operand(b, visit);
            operand(c, visit);
            visit(Slot::Def, dest);
        }
        Inst::ObjectSet { obj, src, .. } => {
            operand(obj, visit);
            operand(src, visit);
        }
        Inst::MakeClosure { dest, env, .. } => {
            for capture in env {
                operand(capture, visit);
            }
            visit(Slot::Def, dest);
        }
        Inst::SetFinalizer { obj, closure } => {
            operand(obj, visit);
            operand(closure, visit);
        }
        Inst::CellNew { dest, init } => {
            operand(init, visit);
            visit(Slot::Def, dest);
        }
        Inst::CellGet { dest, cell } => {
            operand(cell, visit);
            visit(Slot::Def, dest);
        }
        Inst::CellSet { cell, src } => {
            operand(cell, visit);
            operand(src, visit);
        }
        Inst::PushHandler { clause, cont, .. } => {
            operand(clause, visit);
            operand(cont, visit);
        }
        Inst::FindHandler {
            clause,
            cont,
            index,
            ..
        } => {
            visit(Slot::Def, clause);
            visit(Slot::Def, cont);
            visit(Slot::Def, index);
        }
        Inst::GlobalStore { src, .. } => operand(src, visit),
        Inst::ExistentialPack {
            dest,
            payload,
            witnesses,
            ..
        } => {
            operand(payload, visit);
            for witness in witnesses {
                operand(witness, visit);
            }
            visit(Slot::Def, dest);
        }
        Inst::AbortTo { cont, value } => {
            operand(cont, visit);
            operand(value, visit);
        }
    }
}

pub(crate) fn visit_term(term: &mut Term, visit: &mut impl FnMut(Slot, &mut LocalId)) {
    match term {
        Term::Branch { cond: op, .. } | Term::Return(op) => {
            if let Operand::Local(local) = op {
                visit(Slot::Use, local);
            }
        }
        Term::Goto(_, edge_args) => {
            for arg in edge_args {
                if let Operand::Local(local) = arg {
                    visit(Slot::Use, local);
                }
            }
        }
        Term::Trap(_) | Term::UnwindRet => {}
    }
}

/// A block's successors in the flow graph, unwind cleanup entries
/// included.
fn successors(block: &BlockData) -> Vec<usize> {
    let mut out = Vec::new();
    for inst in &block.insts {
        match inst {
            Inst::Call {
                unwind: Some(cleanup),
                ..
            }
            | Inst::CallIndirect {
                unwind: Some(cleanup),
                ..
            } => out.push(*cleanup),
            _ => {}
        }
    }
    match block.term {
        Some(Term::Goto(target, _)) => out.push(target),
        Some(Term::Branch {
            then_block,
            else_block,
            ..
        }) => {
            out.push(then_block);
            out.push(else_block);
        }
        _ => {}
    }
    out
}

/// Renumber `function`'s locals in place onto reusable registers.
/// Fuse `inst t = …; Copy v ← t` pairs where `t` dies at the copy: the
/// instruction writes `v` directly and the copy disappears — the same
/// result a coalescing allocator with lifetime holes would reach
/// (Traub, Holloway & Smith, PLDI 1998), done as a peephole because
/// adjacency makes it trivially sound: the VM reads an instruction's
/// operands before writing its destination, so `v` may even be one of
/// the producer's operands (`i = i + 1` becomes one instruction).
/// Also deletes copies into never-read destinations — a loop
/// statement's discarded Unit result.
fn fuse_adjacent_copies(function: &mut Function) {
    let arity = function.arity;
    let mut uses: FxHashMap<LocalId, u32> = FxHashMap::default();
    let mut param_locals: rustc_hash::FxHashSet<LocalId> = rustc_hash::FxHashSet::default();
    for block in &mut function.blocks {
        param_locals.extend(block.params.iter().copied());
        for inst in &mut block.insts {
            visit_inst(inst, &mut |slot, local| {
                if slot == Slot::Use {
                    *uses.entry(*local).or_insert(0) += 1;
                }
            });
        }
        if let Some(term) = &mut block.term {
            visit_term(term, &mut |_, local| {
                *uses.entry(*local).or_insert(0) += 1;
            });
        }
    }
    for block in &mut function.blocks {
        let mut i = 0;
        while i < block.insts.len() {
            // Dead copy: a destination nothing ever reads.
            if let Inst::Copy { dest, src } = &block.insts[i]
                && *dest >= arity
                && uses.get(dest).copied().unwrap_or(0) == 0
                && !param_locals.contains(dest)
            {
                if let Operand::Local(source) = src
                    && let Some(count) = uses.get_mut(source)
                {
                    *count -= 1;
                }
                block.insts.remove(i);
                continue;
            }
            // Def-copy fusion with the immediately following copy.
            if i + 1 < block.insts.len()
                && let Inst::Copy {
                    dest: fused,
                    src: Operand::Local(temp),
                } = block.insts[i + 1]
                && temp >= arity
                && uses.get(&temp).copied().unwrap_or(0) == 1
                && !param_locals.contains(&temp)
            {
                let mut defs: Vec<LocalId> = Vec::new();
                visit_inst(&mut block.insts[i], &mut |slot, local| {
                    if slot == Slot::Def {
                        defs.push(*local);
                    }
                });
                if defs == [temp] && fused != temp {
                    visit_inst(&mut block.insts[i], &mut |slot, local| {
                        if slot == Slot::Def {
                            *local = fused;
                        }
                    });
                    block.insts.remove(i + 1);
                    // Re-examine the same position: the rewritten
                    // instruction may pair with the next copy in a chain.
                    continue;
                }
            }
            i += 1;
        }
    }
}

/// Reorder blocks into reverse postorder so a join block sits after
/// every predecessor in layout. The linear-position intervals below
/// are only as precise as the layout: with a join placed before an
/// arm (the builder allocates join blocks first), the join's interval
/// falsely covers the arm and affinity coalescing is denied. RPO is
/// the standard layout for exactly this reason (Aho, Sethi & Ullman,
/// §10; every SSA-era compiler linearizes this way). Unreachable
/// blocks keep their relative order at the end.
fn layout_blocks(function: &mut Function) {
    let count = function.blocks.len();
    let mut postorder: Vec<usize> = Vec::with_capacity(count);
    let mut state = vec![0u8; count]; // 0 unvisited, 1 open, 2 done
    // Successors are visited in reverse so a branch's then-arm lands
    // earlier in the final layout than its else-arm — keeping each
    // path's uses linearly close to the path's own blocks.
    let entry_succ = {
        let mut succ = successors(&function.blocks[0]);
        succ.reverse();
        succ
    };
    let mut stack: Vec<(usize, Vec<usize>, usize)> = vec![(0, entry_succ, 0)];
    state[0] = 1;
    while let Some((block, succ, cursor)) = stack.last_mut() {
        if *cursor < succ.len() {
            let next = succ[*cursor];
            *cursor += 1;
            if state[next] == 0 {
                state[next] = 1;
                let mut next_succ = successors(&function.blocks[next]);
                next_succ.reverse();
                stack.push((next, next_succ, 0));
            }
        } else {
            postorder.push(*block);
            state[*block] = 2;
            stack.pop();
        }
    }
    let mut order: Vec<usize> = postorder.into_iter().rev().collect();
    for (block, &visit) in state.iter().enumerate() {
        if visit == 0 {
            order.push(block);
        }
    }
    if order.iter().copied().eq(0..count) {
        return;
    }
    let mut position = vec![0usize; count];
    for (new_index, &old_index) in order.iter().enumerate() {
        position[old_index] = new_index;
    }
    let mut reordered: Vec<BlockData> = Vec::with_capacity(count);
    let mut taken: Vec<Option<BlockData>> = std::mem::take(&mut function.blocks)
        .into_iter()
        .map(Some)
        .collect();
    for &old_index in &order {
        // Every index appears once in a permutation; an empty default
        // keeps positions aligned if that invariant ever broke.
        reordered.push(taken[old_index].take().unwrap_or_default());
    }
    function.blocks = reordered;
    for block in &mut function.blocks {
        for inst in &mut block.insts {
            match inst {
                Inst::Call { unwind, .. } | Inst::CallIndirect { unwind, .. } => {
                    if let Some(cleanup) = unwind {
                        *cleanup = position[*cleanup];
                    }
                }
                _ => {}
            }
        }
        match &mut block.term {
            Some(Term::Goto(target, _)) => *target = position[*target],
            Some(Term::Branch {
                then_block,
                else_block,
                ..
            }) => {
                *then_block = position[*then_block];
                *else_block = position[*else_block];
            }
            _ => {}
        }
    }
}

pub(crate) fn reuse_locals(function: &mut Function) {
    layout_blocks(function);
    fuse_adjacent_copies(function);
    let arity = usize::from(function.arity);
    let n_locals = usize::from(function.n_locals);
    if n_locals <= arity + 1 {
        return;
    }

    // Backward liveness to fixpoint, one dense bitset per block —
    // locals are small dense integers, and the hash-set version of
    // these sets was the top self-time entry of the whole compile.
    // Sets hold only locals >= arity; parameters never move.
    let block_count = function.blocks.len();
    let words = n_locals.div_ceil(64);
    let mut live_in: Vec<Vec<u64>> = vec![vec![0u64; words]; block_count];
    let succ: Vec<Vec<usize>> = function.blocks.iter().map(successors).collect();
    let set = |bits: &mut [u64], local: LocalId| {
        bits[usize::from(local) / 64] |= 1u64 << (usize::from(local) % 64);
    };
    let clear = |bits: &mut [u64], local: LocalId| {
        bits[usize::from(local) / 64] &= !(1u64 << (usize::from(local) % 64));
    };
    let mut changed = true;
    let mut live = vec![0u64; words];
    while changed {
        changed = false;
        for b in (0..block_count).rev() {
            live.fill(0);
            for &s in &succ[b] {
                for (word, incoming) in live.iter_mut().zip(&live_in[s]) {
                    *word |= incoming;
                }
            }
            let block = &mut function.blocks[b];
            if let Some(term) = &mut block.term {
                visit_term(term, &mut |_, local| {
                    set(&mut live, *local);
                });
            }
            for inst in block.insts.iter_mut().rev() {
                // Defs kill first, then uses gen — reverse walk.
                let mut defs: Vec<LocalId> = Vec::new();
                let mut uses: Vec<LocalId> = Vec::new();
                visit_inst(inst, &mut |slot, local| match slot {
                    Slot::Def => defs.push(*local),
                    Slot::Use => uses.push(*local),
                });
                for def in defs {
                    clear(&mut live, def);
                }
                for used in uses {
                    set(&mut live, used);
                }
            }
            for &param in &block.params {
                if usize::from(param) >= arity {
                    clear(&mut live, param);
                }
            }
            if live != live_in[b] {
                std::mem::swap(&mut live_in[b], &mut live);
                changed = true;
            }
        }
    }
    let for_each_bit = |bits: &[u64], f: &mut dyn FnMut(LocalId)| {
        for (index, &word) in bits.iter().enumerate() {
            let mut word = word;
            while word != 0 {
                let bit = word.trailing_zeros() as usize;
                f(u16::try_from(index * 64 + bit).unwrap_or_default());
                word &= word - 1;
            }
        }
    };

    // Live intervals over the blocks in layout order (the order lowering
    // emits them): each local's first and last position where it is
    // defined, used, or live through.
    const UNSET: u32 = u32::MAX;
    let mut start = vec![UNSET; n_locals];
    let mut end = vec![0u32; n_locals];
    // Parameters are defined at entry by the calling convention; their
    // intervals begin at position zero and their registers return to
    // the pool when they die, so a dying parameter can donate its
    // register through a hint (fib's base case returns its parameter's
    // register) and short-lived parameters free their slots.
    start[..arity].fill(0);
    let extend = |local: LocalId, pos: u32, start: &mut Vec<u32>, end: &mut Vec<u32>| {
        let ix = usize::from(local);
        if start[ix] == UNSET || pos < start[ix] {
            start[ix] = pos;
        }
        if pos > end[ix] {
            end[ix] = pos;
        }
    };
    let mut pos: u32 = 0;
    for (b, block) in function.blocks.iter_mut().enumerate() {
        let block_start = pos;
        let block_end = pos + u32::try_from(block.insts.len()).unwrap_or(u32::MAX - 1) + 1;
        for_each_bit(&live_in[b], &mut |local| {
            extend(local, block_start, &mut start, &mut end);
        });
        for &param in &block.params {
            extend(param, block_start, &mut start, &mut end);
        }
        for inst in block.insts.iter_mut() {
            pos += 1;
            visit_inst(inst, &mut |_, local| {
                extend(*local, pos, &mut start, &mut end);
            });
        }
        pos = block_end;
        if let Some(term) = &mut block.term {
            visit_term(term, &mut |_, local| {
                extend(*local, pos, &mut start, &mut end);
            });
        }
        // A local live into any successor is live through this block's
        // exit.
        for &s in &succ[b] {
            for_each_bit(&live_in[s], &mut |local| {
                extend(local, block_end, &mut start, &mut end);
            });
        }
        pos += 1;
    }

    // Affinity groups: every copy pair and every Goto-edge
    // argument/parameter pair prefers one shared register, so the move
    // between them lowers to nothing (register hints — Wimmer &
    // Mössenböck, VEE 2005; edge coalescing — Wimmer & Franz, CGO
    // 2010). Union-find joins the pairs into groups so a two-
    // predecessor join can coalesce with BOTH its arguments (fib's
    // parameter, its base-case join, and its recursive sum all share
    // one register). A group member whose interval genuinely overlaps
    // the group's register simply allocates normally — affinity is a
    // preference, never a constraint.
    let mut affinity: Vec<u16> = (0..function.n_locals).collect();
    fn find_group(affinity: &mut [u16], local: u16) -> u16 {
        let parent = affinity[usize::from(local)];
        if parent == local {
            return local;
        }
        let root = find_group(affinity, parent);
        affinity[usize::from(local)] = root;
        root
    }
    let join_group = |affinity: &mut Vec<u16>, a: u16, b: u16| {
        let ra = find_group(affinity, a);
        let rb = find_group(affinity, b);
        if ra != rb {
            affinity[usize::from(rb)] = ra;
        }
    };
    for block in &function.blocks {
        for inst in &block.insts {
            if let Inst::Copy {
                dest,
                src: Operand::Local(src),
            } = inst
                && usize::from(*dest) >= arity
            {
                join_group(&mut affinity, *dest, *src);
            }
        }
        if let Some(Term::Goto(target, edge_args)) = &block.term {
            for (param, arg) in function.blocks[*target].params.iter().zip(edge_args) {
                if let Operand::Local(source) = arg
                    && usize::from(*param) >= arity
                {
                    join_group(&mut affinity, *param, *source);
                }
            }
        }
    }

    // Interval assignment in start order with a free list. Expired
    // registers return to the pool; overlapping intervals never share
    // except affinity mates meeting exactly at their copy or edge.
    let mut order: Vec<usize> = (arity..n_locals)
        .filter(|&local| start[local] != UNSET)
        .collect();
    order.sort_unstable_by_key(|&local| start[local]);
    let mut map: Vec<LocalId> = (0..function.n_locals).collect::<Vec<u16>>();
    // (interval end, register, holder local), ordered by end as linear
    // scan wants (Poletto & Sarkar 1999): expiry drains the ordered
    // prefix and the group-mate touch below reads the exact-`s` range,
    // so neither walks the whole live set even under high register
    // pressure.
    let mut active: std::collections::BTreeSet<(u32, LocalId, LocalId)> =
        std::collections::BTreeSet::new();
    let mut free: Vec<LocalId> = Vec::new();
    let mut next = function.arity;
    // Reservations only matter for genuine affinity (two or more
    // members); a singleton "group" reserving its register forever
    // would starve ordinary reuse.
    let mut group_size: FxHashMap<u16, u32> = FxHashMap::default();
    for local in 0..function.n_locals {
        *group_size
            .entry(find_group(&mut affinity, local))
            .or_insert(0) += 1;
    }
    // Each real group's preferred register, established by its first
    // assigned member; parameters claim their groups up front.
    let mut group_register: FxHashMap<u16, u16> = FxHashMap::default();
    // The registers those groups hold, mirrored as a set: group
    // claims only ever insert, so the mirror updates at the two claim
    // sites instead of being rebuilt per interval.
    let mut reserved: rustc_hash::FxHashSet<u16> = rustc_hash::FxHashSet::default();
    for param in 0..function.arity {
        let group = find_group(&mut affinity, param);
        if group_size.get(&group).copied().unwrap_or(0) > 1 {
            group_register.entry(group).or_insert_with(|| {
                reserved.insert(param);
                param
            });
        }
        if end[usize::from(param)] > 0 {
            active.insert((end[usize::from(param)], param, param));
        } else {
            // Never read: the calling convention still writes the slot,
            // but the register is free for locals from the start.
            free.push(param);
        }
    }
    for local in order {
        let s = start[local];
        while let Some(&(active_end, register, holder)) = active.first() {
            if active_end >= s {
                break;
            }
            active.remove(&(active_end, register, holder));
            free.push(register);
        }
        let group = find_group(&mut affinity, u16::try_from(local).unwrap_or_default());
        let wanted = group_register.get(&group).copied();
        let register = wanted
            .and_then(|wanted| {
                // A group mate may still be active, its interval ending
                // exactly where this one starts (the copy or the edge):
                // release its register across the touch. Same-position
                // sharing is safe because the VM reads an instruction's
                // operands before writing its destination; a def-only
                // mate (start == end == s) must not share, so require
                // the holder's interval to have begun earlier.
                // Expiry already removed everything ending before `s`,
                // so touching mates sit in the exact-`s` range.
                let touch = active
                    .range((s, 0, 0)..=(s, LocalId::MAX, LocalId::MAX))
                    .copied()
                    .find(|&(_, register, holder)| {
                        register == wanted
                            && start[usize::from(holder)] < s
                            && find_group(&mut affinity, holder) == group
                    });
                if let Some(entry) = touch {
                    active.remove(&entry);
                    return Some(wanted);
                }
                // Or the register may simply be free.
                free.iter()
                    .position(|&register| register == wanted)
                    .map(|ix| free.swap_remove(ix))
            })
            .unwrap_or_else(|| {
                // Prefer a register no group is waiting on, so affinity
                // mates that start later still find theirs available —
                // a fresh register beats stealing a reservation (one
                // occasional extra frame slot against a move on every
                // loop iteration).
                let choice = free
                    .iter()
                    .rposition(|register| !reserved.contains(register))
                    .map(|ix| free.swap_remove(ix));
                choice.unwrap_or_else(|| {
                    let register = next;
                    next += 1;
                    register
                })
            });
        map[local] = register;
        if group_size.get(&group).copied().unwrap_or(0) > 1 {
            group_register.entry(group).or_insert_with(|| {
                reserved.insert(register);
                register
            });
        }
        active.insert((
            end[local],
            register,
            u16::try_from(local).unwrap_or_default(),
        ));
    }

    // Rewrite every local through the map, block parameters included.
    for block in &mut function.blocks {
        for param in &mut block.params {
            *param = map[usize::from(*param)];
        }
        for inst in &mut block.insts {
            visit_inst(inst, &mut |_, local| *local = map[usize::from(*local)]);
        }
        if let Some(term) = &mut block.term {
            visit_term(term, &mut |_, local| *local = map[usize::from(*local)]);
        }
    }
    function.n_locals = next.max(function.arity).max(1);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::mir::{BlockData, CmpKind, Constant, ScalarOp};

    fn copy(dest: LocalId, src: Operand) -> Inst {
        Inst::Copy { dest, src }
    }

    fn add(dest: LocalId, a: Operand, b: Operand) -> Inst {
        Inst::Scalar {
            dest,
            op: ScalarOp::IntAdd,
            a,
            b: Some(b),
        }
    }

    fn local(id: LocalId) -> Operand {
        Operand::Local(id)
    }

    fn int(value: i64) -> Operand {
        Operand::Const(Constant::Int(value))
    }

    fn function(arity: u16, n_locals: u16, blocks: Vec<BlockData>) -> Function {
        Function {
            name: "test".into(),
            arity,
            n_locals,
            blocks,
        }
    }

    #[test]
    fn disjoint_temporaries_share_a_register() {
        // t1 = 1; t2 = t1 + 1; t3 = t2 + 1; return t3 — each temp dies
        // as the next is defined, so three temps fit in two registers.
        let mut f = function(
            0,
            3,
            vec![BlockData {
                params: Vec::new(),
                insts: vec![
                    copy(0, int(1)),
                    add(1, local(0), int(1)),
                    add(2, local(1), int(1)),
                ],
                term: Some(Term::Return(local(2))),
            }],
        );
        reuse_locals(&mut f);
        assert!(f.n_locals <= 2, "expected reuse, got {} locals", f.n_locals);
    }

    #[test]
    fn overlapping_intervals_under_pressure_stay_distinct() {
        // 64 locals defined in order, then used in reverse: every pair
        // overlaps, so all 64 must hold distinct registers while live —
        // the widest active set the ordered expiry structure sees.
        let width: u16 = 64;
        let mut insts: Vec<Inst> = (0..width).map(|i| copy(i, int(i64::from(i)))).collect();
        for k in 0..width {
            insts.push(add(width + k, local(width - 1 - k), int(1)));
        }
        let result = local(width + width - 1);
        let mut f = function(
            0,
            width * 2,
            vec![BlockData {
                params: Vec::new(),
                insts,
                term: Some(Term::Return(result)),
            }],
        );
        reuse_locals(&mut f);
        let mut defs = Vec::new();
        for i in 0..usize::from(width) {
            let Inst::Copy { dest, .. } = &f.blocks[0].insts[i] else {
                panic!("definition changed shape");
            };
            defs.push(*dest);
        }
        let mut sorted = defs.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), usize::from(width), "live registers collided");
        for k in 0..usize::from(width) {
            let Inst::Scalar {
                a: Operand::Local(read),
                ..
            } = &f.blocks[0].insts[usize::from(width) + k]
            else {
                panic!("use changed shape");
            };
            assert_eq!(
                *read,
                defs[usize::from(width) - 1 - k],
                "use no longer reads its definition's register"
            );
        }
    }

    #[test]
    fn copy_chains_coalesce_onto_one_register() {
        // t0 = 1; t3 = 9; t1 = copy t0; t2 = t1 + t3 — the copy is
        // t0's last use (and not adjacent to t0's producer, so fusion
        // leaves it in place), so t1 takes t0's register and lowering
        // elides the move (register hints — Wimmer & Mössenböck,
        // VEE 2005).
        let mut f = function(
            0,
            4,
            vec![BlockData {
                params: Vec::new(),
                insts: vec![
                    copy(0, int(1)),
                    copy(3, int(9)),
                    copy(1, local(0)),
                    add(2, local(1), local(3)),
                ],
                term: Some(Term::Return(local(2))),
            }],
        );
        reuse_locals(&mut f);
        let Inst::Copy { dest, src } = &f.blocks[0].insts[2] else {
            panic!("copy changed shape");
        };
        assert_eq!(
            Operand::Local(*dest),
            *src,
            "copy source and destination should share a register"
        );
    }

    #[test]
    fn adjacent_assignment_copies_fuse_into_their_producer() {
        // t1 = t0 + 1; t0 = copy t1 — the shape of `i = i + 1`: the
        // producer writes the assigned local directly and the copy
        // disappears.
        let mut f = function(
            0,
            2,
            vec![BlockData {
                params: Vec::new(),
                insts: vec![copy(0, int(5)), add(1, local(0), int(1)), copy(0, local(1))],
                term: Some(Term::Return(local(0))),
            }],
        );
        reuse_locals(&mut f);
        assert_eq!(
            f.blocks[0].insts.len(),
            2,
            "assignment copy should fuse away: {:?}",
            f.blocks[0].insts
        );
        assert!(
            matches!(f.blocks[0].insts[1], Inst::Scalar { dest: 0, .. }),
            "producer should write the assigned local directly"
        );
    }

    #[test]
    fn edge_arguments_coalesce_onto_block_parameters() {
        // b0: t1 = 1 + 1; goto b1(t1) — b1(p): return p. The argument
        // dies at the edge, so the parameter takes its register and the
        // edge move lowers to nothing.
        let mut f = Function {
            name: "edge".into(),
            arity: 0,
            n_locals: 2,
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: vec![add(0, int(1), int(1))],
                    term: Some(Term::Goto(1, vec![local(0)])),
                },
                BlockData {
                    params: vec![1],
                    insts: vec![],
                    term: Some(Term::Return(local(1))),
                },
            ],
        };
        reuse_locals(&mut f);
        let Some(Term::Goto(_, edge_args)) = &f.blocks[0].term else {
            panic!("goto changed shape");
        };
        assert_eq!(
            edge_args[0],
            Operand::Local(f.blocks[1].params[0]),
            "edge argument and parameter should share a register"
        );
    }

    #[test]
    fn parameters_keep_their_registers() {
        let mut f = function(
            2,
            4,
            vec![BlockData {
                params: Vec::new(),
                insts: vec![add(2, local(0), local(1)), add(3, local(2), local(0))],
                term: Some(Term::Return(local(3))),
            }],
        );
        reuse_locals(&mut f);
        let BlockData { insts, .. } = &f.blocks[0];
        let Inst::Scalar { a, b, .. } = &insts[0] else {
            panic!("first inst changed shape");
        };
        assert_eq!((a, b), (&local(0), &Some(local(1))));
    }

    #[test]
    fn value_live_across_a_loop_is_not_reused_inside_it() {
        // b0: x = 7; goto b1
        // b1: t = x + 1; branch t -> b1 | b2   (x live around the back edge)
        // b2: return x
        let mut f = function(
            0,
            2,
            vec![
                BlockData {
                    params: Vec::new(),
                    insts: vec![copy(0, int(7))],
                    term: Some(Term::Goto(1, Vec::new())),
                },
                BlockData {
                    params: Vec::new(),
                    insts: vec![Inst::Scalar {
                        dest: 1,
                        op: ScalarOp::IntCmp(CmpKind::Eq),
                        a: local(0),
                        b: Some(int(1)),
                    }],
                    term: Some(Term::Branch {
                        cond: local(1),
                        then_block: 1,
                        else_block: 2,
                    }),
                },
                BlockData {
                    params: Vec::new(),
                    insts: vec![],
                    term: Some(Term::Return(local(0))),
                },
            ],
        );
        reuse_locals(&mut f);
        // x and t are simultaneously live inside the loop: they must hold
        // distinct registers.
        let Inst::Scalar { dest, a, .. } = &f.blocks[1].insts[0] else {
            panic!("loop inst changed shape");
        };
        assert_ne!(
            Operand::Local(*dest),
            *a,
            "loop temp clobbered the loop-carried value"
        );
    }

    #[test]
    fn cleanup_only_values_stay_live_across_the_call() {
        // b0: r = 5; c = call f() unwind-> b2; return c
        // b2 (cleanup): free r; UnwindRet — r's only use is the cleanup
        // path, so it must survive the call.
        let mut f = function(
            0,
            2,
            vec![
                BlockData {
                    params: Vec::new(),
                    insts: vec![
                        copy(0, int(5)),
                        Inst::Call {
                            dest: 1,
                            func: 0,
                            args: vec![],
                            unwind: Some(1),
                        },
                    ],
                    term: Some(Term::Return(local(1))),
                },
                BlockData {
                    params: Vec::new(),
                    insts: vec![Inst::Free { src: local(0) }],
                    term: Some(Term::UnwindRet),
                },
            ],
        );
        reuse_locals(&mut f);
        let Inst::Call { dest, .. } = &f.blocks[0].insts[1] else {
            panic!("call changed shape");
        };
        let Inst::Free { src } = &f.blocks[1].insts[0] else {
            panic!("cleanup changed shape");
        };
        assert_ne!(
            Operand::Local(*dest),
            *src,
            "call result reused the register of a cleanup-live value"
        );
    }
}
