//! Target-bytecode fusion for checked indexed reads.
//!
//! This pass runs after MIR lowering: it recognizes compiler-emitted VM
//! shapes, replaces their hot path with `CheckedIndexedLoad`, and retains
//! an exact copy of the original sequence as the source-owned failure path.

use rustc_hash::FxHashSet;
use talk_vm::{Chunk, CmpOp, Constant, Insn, MemKind, Module};

#[derive(Clone, Copy)]
struct BoundsHelper {
    length_field: u16,
}

#[derive(Clone, Copy)]
struct CheckedLoadMatch {
    start: usize,
    collection: u16,
    index: u16,
    length_field: u16,
    /// `base`'s offset in the collection itself: the compiler folds the
    /// `storage.base` chain to one read (ADR 0046), so the emitted
    /// sequence carries the container offset directly.
    base_offset: u16,
    dest: u16,
    kind: MemKind,
}

fn constant_is(module: &Module, field: u16, expected: Constant) -> bool {
    if field & talk_vm::RK_CONST == 0 {
        return false;
    }
    module
        .consts
        .get(usize::from(field & talk_vm::RK_INDEX))
        .is_some_and(|constant| *constant == expected)
}

/// Recognize the canonical bytecode shape of a two-argument helper whose
/// successful result means `0 <= index < collection.length`. The failure
/// region is deliberately opaque: callers retain the original call there,
/// so its Talk-level effect and unwind behavior stay authoritative.
fn bounds_helper(module: &Module, chunk: &Chunk) -> Option<BoundsHelper> {
    let [
        Insn::Cmp {
            dest: lower_cond,
            a: 1,
            b: zero,
            op: CmpOp::Lt,
        },
        Insn::Branch {
            cond: first_cond,
            then_target: lower_true,
            else_target: upper_start,
        },
        Insn::Const {
            dest: true_reg,
            k: true_k,
        },
        Insn::Jump { target: merge },
        Insn::Field {
            dest: length,
            src: 0,
            offset: length_field,
            ..
        },
        Insn::Cmp {
            dest: upper_cond,
            a: 1,
            b: upper_length,
            op: CmpOp::Ge,
        },
        Insn::Branch {
            cond: merged_cond,
            then_target: failure,
            else_target: success,
        },
        ..,
    ] = chunk.code.as_slice()
    else {
        return None;
    };
    if chunk.arity != 2
        || lower_cond != first_cond
        || *lower_true != 2
        || *upper_start != 4
        || *merge != 6
        || true_reg != upper_cond
        || true_reg != merged_cond
        || length != upper_length
        || !constant_is(module, *zero, Constant::I64(0))
        || module.consts.get(*true_k as usize) != Some(&Constant::Bool(true))
        || failure == success
    {
        return None;
    }
    let success = usize::try_from(*success).ok()?;
    let success_end = success.checked_add(2)?;
    let [Insn::Const { dest, k }, Insn::Ret { src }] = chunk.code.get(success..success_end)? else {
        return None;
    };
    if dest != src || module.consts.get(*k as usize) != Some(&Constant::Void) {
        return None;
    }
    Some(BoundsHelper {
        length_field: *length_field,
    })
}

fn chunk_targets(module: &Module, chunk: &Chunk) -> FxHashSet<usize> {
    let mut targets = FxHashSet::default();
    for insn in &chunk.code {
        match insn {
            Insn::Jump { target } => {
                targets.insert(*target as usize);
            }
            Insn::Branch {
                then_target,
                else_target,
                ..
            } => {
                targets.insert(*then_target as usize);
                targets.insert(*else_target as usize);
            }
            Insn::Switch {
                targets_start,
                targets_len,
                ..
            } => {
                let start = *targets_start as usize;
                let end = start + *targets_len as usize;
                targets.extend(
                    module.switch_pool[start..end]
                        .iter()
                        .map(|target| *target as usize),
                );
            }
            Insn::CheckedIndexedLoad { failure_target, .. } => {
                targets.insert(*failure_target as usize);
            }
            _ => {}
        }
    }
    for &(suspension, cleanup) in &chunk.unwind {
        targets.insert(suspension as usize);
        targets.insert(cleanup as usize);
    }
    targets
}

fn checked_load_match(
    module: &Module,
    chunk: &Chunk,
    helpers: &[Option<BoundsHelper>],
    start: usize,
    targets: &FxHashSet<usize>,
) -> Option<CheckedLoadMatch> {
    let end = start.checked_add(6)?;
    if end >= chunk.code.len() {
        return None;
    }
    let [
        Insn::Call {
            chunk: helper,
            args_start,
            args_len: 2,
            ..
        },
        Insn::Field {
            dest: base,
            src: base_owner,
            offset: base_offset,
            layout: base_layout,
        },
        Insn::Const { dest: scale, k },
        Insn::Mul {
            dest: scaled,
            a: mul_a,
            b: mul_b,
        },
        Insn::Add {
            dest: address,
            a: add_base,
            b: add_offset,
        },
        Insn::Load { dest, ptr, kind },
    ] = chunk.code.get(start..end)?
    else {
        return None;
    };
    let helper = helpers.get(*helper as usize)?.as_ref()?;
    let args_start = usize::try_from(*args_start).ok()?;
    let [collection, index] = module.arg_pool.get(args_start..args_start + 2)? else {
        return None;
    };
    let width = match kind {
        MemKind::Byte => 1,
        MemKind::I64 | MemKind::F64 | MemKind::Bool | MemKind::Ptr | MemKind::Boxed => 8,
    };
    let scale_matches = module.consts.get(*k as usize) == Some(&Constant::I64(width));
    let multiply_matches =
        (*mul_a == *index && *mul_b == *scale) || (*mul_b == *index && *mul_a == *scale);
    if collection & talk_vm::RK_CONST != 0
        || index & talk_vm::RK_CONST != 0
        // `base` is one slot at a container offset; a spliced member
        // would need materialization.
        || *base_layout != talk_vm::NO_LAYOUT
        || base_owner != collection
        || !scale_matches
        || !multiply_matches
        || add_base != base
        || add_offset != scaled
        || ptr != address
        || (start + 1..start + 6).any(|pc| targets.contains(&pc))
    {
        return None;
    }
    Some(CheckedLoadMatch {
        start,
        collection: *collection,
        index: *index,
        length_field: helper.length_field,
        base_offset: *base_offset,
        dest: *dest,
        kind: *kind,
    })
}

/// Fuse the VM's canonical checked indexed-read sequence without teaching it
/// about Array or any source-level name. Success uses one semantic opcode;
/// failure jumps to an appended copy of the original sequence, preserving the
/// original helper call and therefore Talk's catchable `'panic` behavior.
pub(super) fn run(module: &mut Module) -> u64 {
    let helpers: Vec<Option<BoundsHelper>> = module
        .chunks
        .iter()
        .map(|chunk| bounds_helper(module, chunk))
        .collect();
    let mut applied = 0u64;
    for chunk_index in 0..module.chunks.len() {
        let targets = chunk_targets(module, &module.chunks[chunk_index]);
        let original_len = module.chunks[chunk_index].code.len();
        let matches: Vec<CheckedLoadMatch> = (0..original_len.saturating_sub(5))
            .filter_map(|start| {
                checked_load_match(
                    module,
                    &module.chunks[chunk_index],
                    &helpers,
                    start,
                    &targets,
                )
            })
            .collect();
        if matches.is_empty() || module.chunks[chunk_index].n_regs > u16::MAX - 2 {
            continue;
        }
        let length_reg = module.chunks[chunk_index].n_regs;
        let base_reg = length_reg + 1;
        module.chunks[chunk_index].n_regs += 2;
        for matched in matches {
            let fallback = u32::try_from(module.chunks[chunk_index].code.len()).unwrap_or_default();
            let continuation = u32::try_from(matched.start + 6).unwrap_or_default();
            let original =
                module.chunks[chunk_index].code[matched.start..matched.start + 6].to_vec();
            module.chunks[chunk_index].code.extend(original);
            module.chunks[chunk_index].code.push(Insn::Jump {
                target: continuation,
            });
            module.chunks[chunk_index].code[matched.start] = Insn::Field {
                dest: length_reg,
                src: matched.collection,
                offset: matched.length_field,
                layout: talk_vm::NO_LAYOUT,
            };
            module.chunks[chunk_index].code[matched.start + 1] = Insn::Field {
                dest: base_reg,
                src: matched.collection,
                offset: matched.base_offset,
                layout: talk_vm::NO_LAYOUT,
            };
            module.chunks[chunk_index].code[matched.start + 2] = Insn::CheckedIndexedLoad {
                dest: matched.dest,
                base: base_reg,
                index: matched.index,
                length: length_reg,
                kind: matched.kind,
                failure_target: fallback,
            };
            module.chunks[chunk_index].code[matched.start + 3] = Insn::Jump {
                target: continuation,
            };
            applied += 1;
        }
    }
    applied
}

#[cfg(test)]
mod tests {
    use super::*;

    fn checked_load_module() -> Module {
        let caller = Chunk {
            name: "read".into(),
            code: vec![
                Insn::Call {
                    dest: 2,
                    chunk: 1,
                    args_start: 0,
                    args_len: 2,
                },
                Insn::Field {
                    dest: 0,
                    src: 0,
                    offset: 0,
                    layout: talk_vm::NO_LAYOUT,
                },
                Insn::Const { dest: 3, k: 3 },
                Insn::Mul {
                    dest: 4,
                    a: 1,
                    b: 3,
                },
                Insn::Add {
                    dest: 2,
                    a: 0,
                    b: 4,
                },
                Insn::Load {
                    dest: 1,
                    ptr: 2,
                    kind: MemKind::I64,
                },
                Insn::Ret { src: 1 },
            ],
            arity: 2,
            n_regs: 5,
            unwind: vec![],
        };
        let helper = Chunk {
            name: "bounds".into(),
            code: vec![
                Insn::Cmp {
                    dest: 2,
                    a: 1,
                    b: talk_vm::RK_CONST,
                    op: CmpOp::Lt,
                },
                Insn::Branch {
                    cond: 2,
                    then_target: 2,
                    else_target: 4,
                },
                Insn::Const { dest: 3, k: 1 },
                Insn::Jump { target: 6 },
                Insn::Field {
                    dest: 4,
                    src: 0,
                    offset: 1,
                    layout: talk_vm::NO_LAYOUT,
                },
                Insn::Cmp {
                    dest: 3,
                    a: 1,
                    b: 4,
                    op: CmpOp::Ge,
                },
                Insn::Branch {
                    cond: 3,
                    then_target: 7,
                    else_target: 8,
                },
                Insn::Trap { message: 0 },
                Insn::Const { dest: 4, k: 2 },
                Insn::Ret { src: 4 },
            ],
            arity: 2,
            n_regs: 5,
            unwind: vec![],
        };
        Module {
            chunks: vec![caller, helper],
            consts: vec![
                Constant::I64(0),
                Constant::Bool(true),
                Constant::Void,
                Constant::I64(8),
            ],
            arg_pool: vec![0, 1],
            traps: vec!["bounds".into()],
            ..Module::default()
        }
    }

    #[test]
    fn fuses_checked_indexed_load_and_keeps_original_failure_call() {
        let mut module = checked_load_module();
        assert_eq!(run(&mut module), 1);
        assert_eq!(module.chunks[0].n_regs, 7);
        // The compiler already folded `storage.base` to one container
        // offset (ADR 0046); the fused hot path re-reads it fresh.
        assert!(matches!(
            module.chunks[0].code[1],
            Insn::Field {
                dest: 6,
                src: 0,
                offset: 0,
                layout: talk_vm::NO_LAYOUT,
            }
        ));
        assert!(matches!(
            module.chunks[0].code[2],
            Insn::CheckedIndexedLoad {
                dest: 1,
                base: 6,
                index: 1,
                length: 5,
                kind: MemKind::I64,
                failure_target: 7,
            }
        ));
        assert!(matches!(
            module.chunks[0].code[7],
            Insn::Call { chunk: 1, .. }
        ));
        assert!(matches!(
            module.chunks[0].code[13],
            Insn::Jump { target: 6 }
        ));
    }

    #[test]
    fn does_not_fuse_across_an_interior_control_flow_target() {
        let mut module = checked_load_module();
        module.chunks[0].code.push(Insn::Jump { target: 4 });
        assert_eq!(run(&mut module), 0);
    }
}
