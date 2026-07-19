//! Small-function inlining over the built MIR program.
//!
//! Core's scalar operators (`add`, `equals`, `not`, …) have
//! single-instruction bodies, but every call site still paid a full
//! frame push, argument copy, and return delivery — arithmetic
//! dominated the call counts (millions of one-instruction frames per
//! test run). This pass splices such bodies into their callers
//! (procedure integration in the classic sense — Scheifler, CACM
//! 1977; Allen & Cocke's catalogue of transformations, 1971).
//!
//! Candidates are deliberately narrow: at most a handful of
//! instructions, all from the primitive whitelist (scalar ops,
//! loads/stores, field/payload reads), terminators limited to
//! branches, jumps, returns, and traps, and no writes to parameters.
//! No calls means no unwind edges, no effect machinery, and no
//! recursion — a candidate body is final the moment the program is
//! built, so one pass over every caller suffices. Straight-line
//! bodies splice in place; branching bodies (a bounds-checked `get`:
//! compare, trap, load) splice as blocks, with the caller's block
//! split at the call and every callee `Return` rejoining after it.

use rustc_hash::FxHashMap;

use super::mir::{FuncId, Function, Inst, LocalId, Operand, Program, Term};

/// Upper bounds on a candidate body. Small enough that the splice
/// always beats the call it replaces.
const MAX_INLINE_INSTS: usize = 8;
const MAX_INLINE_BLOCKS: usize = 4;

struct Candidate {
    arity: u16,
    n_locals: u16,
    blocks: Vec<super::mir::BlockData>,
}

/// Whether an instruction may appear in an inlined body: primitive,
/// call-free, and frame-independent (nothing that reads the executing
/// closure's environment or the handler stack).
fn primitive(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Copy { .. }
            | Inst::Scalar { .. }
            | Inst::Load { .. }
            | Inst::Store { .. }
            | Inst::MemCopy { .. }
            | Inst::PtrAdd { .. }
            | Inst::TupleGet { .. }
            | Inst::GetTag { .. }
            | Inst::GetPayload { .. }
            | Inst::GetField { .. }
            | Inst::IsUnique { .. }
    )
}

/// The whitelist's destination locals and operand slots. Candidacy
/// rejects any body whose destination is a parameter, so `dest` maps
/// unconditionally while operands substitute through the call
/// arguments (which may be constants).
fn remap_inst(
    inst: &mut Inst,
    dest: &mut dyn FnMut(&mut LocalId),
    op: &mut dyn FnMut(&mut Operand),
) {
    match inst {
        Inst::Copy { dest: d, src } => {
            op(src);
            dest(d);
        }
        Inst::Scalar { dest: d, a, b, .. } => {
            op(a);
            if let Some(b) = b {
                op(b);
            }
            dest(d);
        }
        Inst::Load { dest: d, ptr, .. } => {
            op(ptr);
            dest(d);
        }
        Inst::Store { ptr, src, .. } => {
            op(ptr);
            op(src);
        }
        Inst::MemCopy { from, to, len } => {
            op(from);
            op(to);
            op(len);
        }
        Inst::PtrAdd {
            dest: d,
            ptr,
            offset,
            ..
        } => {
            op(ptr);
            op(offset);
            dest(d);
        }
        Inst::TupleGet { dest: d, src, .. }
        | Inst::GetTag { dest: d, src }
        | Inst::GetPayload { dest: d, src, .. }
        | Inst::GetField { dest: d, src, .. }
        | Inst::IsUnique { dest: d, src } => {
            op(src);
            dest(d);
        }
        // `primitive` admits nothing else into a candidate body.
        _ => unreachable!("non-primitive instruction in an inline candidate"),
    }
}

fn candidate(function: &Function) -> Option<Candidate> {
    if function.blocks.len() > MAX_INLINE_BLOCKS {
        return None;
    }
    let total: usize = function.blocks.iter().map(|block| block.insts.len()).sum();
    if total > MAX_INLINE_INSTS {
        return None;
    }
    let arity = function.arity;
    let mut writes_param = false;
    for block in &function.blocks {
        match block.term {
            Some(Term::Goto(_, _) | Term::Branch { .. } | Term::Return(_) | Term::Trap(_)) => {}
            _ => return None,
        }
        if !block.insts.iter().all(primitive) {
            return None;
        }
        // A body that writes a parameter can't take call arguments by
        // substitution (an argument operand may be a constant).
        for inst in &block.insts {
            let mut probe = inst.clone();
            remap_inst(
                &mut probe,
                &mut |dest| {
                    if *dest < arity {
                        writes_param = true;
                    }
                },
                &mut |_| {},
            );
        }
    }
    if writes_param {
        return None;
    }
    Some(Candidate {
        arity,
        n_locals: function.n_locals,
        blocks: function.blocks.clone(),
    })
}

fn remap(op: Operand, args: &[Operand], base: u16, arity: u16) -> Operand {
    match op {
        Operand::Local(local) if local < arity => args[usize::from(local)],
        Operand::Local(local) => Operand::Local(base + (local - arity)),
        constant => constant,
    }
}

/// Inline every candidate call in `program`, to a fixpoint: splicing
/// `_load` into `get` makes `get` itself call-free and a candidate for
/// the next round. Rounds are bounded — each strictly shrinks the set
/// of call edges into candidates, and the chains are shallow.
pub(crate) fn inline_small(program: &mut Program) {
    for _ in 0..4 {
        if !inline_round(program) {
            break;
        }
    }
}

fn inline_round(program: &mut Program) -> bool {
    let candidates: FxHashMap<FuncId, Candidate> = program
        .functions
        .iter()
        .enumerate()
        .filter_map(|(id, function)| candidate(function).map(|c| (id, c)))
        .collect();
    if candidates.is_empty() {
        return false;
    }
    let mut changed = false;
    for function in &mut program.functions {
        // Iterate by index: splicing appends callee and join blocks,
        // and the join block (holding the call's tail) is scanned in a
        // later iteration for further candidate calls.
        let mut b = 0;
        while b < function.blocks.len() {
            let call_at = function.blocks[b].insts.iter().position(
                |inst| matches!(inst, Inst::Call { func, .. } if candidates.contains_key(func)),
            );
            let Some(position) = call_at else {
                b += 1;
                continue;
            };
            let (dest, func, args) = {
                let Inst::Call {
                    dest, func, args, ..
                } = &function.blocks[b].insts[position]
                else {
                    unreachable!("position found a call");
                };
                (*dest, *func, args.clone())
            };
            #[allow(clippy::expect_used)]
            let body = candidates.get(&func).expect("membership checked above");
            let base = function.n_locals;
            function.n_locals = function.n_locals.saturating_add(body.n_locals - body.arity);

            // Straight-line bodies splice in place — no block split, no
            // jump chain — the overwhelmingly common case (scalar
            // operators).
            if let [only] = body.blocks.as_slice()
                && let Some(Term::Return(value)) = &only.term
            {
                let mut splice = Vec::with_capacity(only.insts.len() + 1);
                for body_inst in &only.insts {
                    let mut copy = body_inst.clone();
                    remap_inst(
                        &mut copy,
                        &mut |d: &mut LocalId| *d = base + (*d - body.arity),
                        &mut |o: &mut Operand| *o = remap(*o, &args, base, body.arity),
                    );
                    splice.push(copy);
                }
                splice.push(Inst::Copy {
                    dest,
                    src: remap(*value, &args, base, body.arity),
                });
                function.blocks[b].insts.splice(position..=position, splice);
                changed = true;
                // Rescan the same block: later insts may hold more
                // candidate calls, and the spliced body holds none.
                continue;
            }

            let block_base = function.blocks.len();
            let join = block_base + body.blocks.len();
            // Split the caller block: everything after the call moves to
            // the join block, and the call is replaced by a jump into the
            // spliced entry.
            let tail: Vec<Inst> = function.blocks[b].insts.split_off(position + 1);
            function.blocks[b].insts.pop();
            let term = function.blocks[b]
                .term
                .replace(Term::Goto(block_base, Vec::new()));
            for body_block in &body.blocks {
                let params: Vec<super::mir::LocalId> = body_block
                    .params
                    .iter()
                    .map(|param| base + (*param - body.arity))
                    .collect();
                let mut insts = Vec::with_capacity(body_block.insts.len());
                for body_inst in &body_block.insts {
                    let mut copy = body_inst.clone();
                    remap_inst(
                        &mut copy,
                        &mut |d: &mut LocalId| *d = base + (*d - body.arity),
                        &mut |o: &mut Operand| *o = remap(*o, &args, base, body.arity),
                    );
                    insts.push(copy);
                }
                let term = match &body_block.term {
                    Some(Term::Goto(target, edge_args)) => Some(Term::Goto(
                        target + block_base,
                        edge_args
                            .iter()
                            .map(|arg| remap(*arg, &args, base, body.arity))
                            .collect(),
                    )),
                    Some(Term::Branch {
                        cond,
                        then_block,
                        else_block,
                    }) => Some(Term::Branch {
                        cond: remap(*cond, &args, base, body.arity),
                        then_block: then_block + block_base,
                        else_block: else_block + block_base,
                    }),
                    Some(Term::Return(value)) => {
                        // The callee's return becomes the call's result
                        // delivery plus a jump past the splice.
                        insts.push(Inst::Copy {
                            dest,
                            src: remap(*value, &args, base, body.arity),
                        });
                        Some(Term::Goto(join, Vec::new()))
                    }
                    Some(Term::Trap(message)) => Some(Term::Trap(message)),
                    other => other.clone(),
                };
                function.blocks.push(super::mir::BlockData {
                    params,
                    insts,
                    term,
                });
            }
            function.blocks.push(super::mir::BlockData {
                params: Vec::new(),
                insts: tail,
                term,
            });
            changed = true;
            // Rescan this block: nothing before `position` was a
            // candidate call, so move on; the join block comes later.
            b += 1;
        }
    }
    changed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::mir::{BlockData, Constant, ScalarOp};

    fn local(id: LocalId) -> Operand {
        Operand::Local(id)
    }

    fn int(value: i64) -> Operand {
        Operand::Const(Constant::Int(value))
    }

    /// Core-style `add`: one scalar instruction over its parameters.
    fn scalar_add() -> Function {
        Function {
            name: "add".into(),
            arity: 2,
            n_locals: 3,
            blocks: vec![BlockData {
                params: Vec::new(),
                insts: vec![Inst::Scalar {
                    dest: 2,
                    op: ScalarOp::IntAdd,
                    a: local(0),
                    b: Some(local(1)),
                }],
                term: Some(Term::Return(local(2))),
            }],
        }
    }

    fn caller(insts: Vec<Inst>, ret: Operand) -> Function {
        Function {
            name: "caller".into(),
            arity: 0,
            n_locals: 2,
            blocks: vec![BlockData {
                params: Vec::new(),
                insts,
                term: Some(Term::Return(ret)),
            }],
        }
    }

    #[test]
    fn scalar_call_becomes_the_scalar_instruction() {
        let mut program = Program {
            functions: vec![
                scalar_add(),
                caller(
                    vec![Inst::Call {
                        dest: 0,
                        func: 0,
                        args: vec![int(1), int(2)],
                        unwind: None,
                    }],
                    local(0),
                ),
            ],
            entry: 1,
            global_slots: 0,
        };
        inline_small(&mut program);
        let insts = &program.functions[1].blocks[0].insts;
        assert!(
            !insts.iter().any(|inst| matches!(inst, Inst::Call { .. })),
            "call survived inlining: {insts:?}"
        );
        // Constant arguments substituted straight into the scalar op.
        assert!(
            insts.iter().any(|inst| matches!(
                inst,
                Inst::Scalar {
                    a: Operand::Const(Constant::Int(1)),
                    b: Some(Operand::Const(Constant::Int(2))),
                    ..
                }
            )),
            "arguments not substituted: {insts:?}"
        );
    }

    #[test]
    fn branching_bodies_splice_as_blocks() {
        // A bounds-checked read: cmp, branch to trap or load, return —
        // the `get` shape. The call disappears, the trap block arrives,
        // and the caller's tail runs after the join.
        let checked_get = Function {
            name: "get".into(),
            arity: 1,
            n_locals: 3,
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: vec![Inst::Scalar {
                        dest: 1,
                        op: ScalarOp::IntCmp(crate::backend::mir::CmpKind::Lt),
                        a: local(0),
                        b: Some(int(0)),
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
                    term: Some(Term::Trap("index out of bounds")),
                },
                BlockData {
                    params: Vec::new(),
                    insts: vec![Inst::Scalar {
                        dest: 2,
                        op: ScalarOp::IntAdd,
                        a: local(0),
                        b: Some(int(10)),
                    }],
                    term: Some(Term::Return(local(2))),
                },
            ],
        };
        let mut program = Program {
            functions: vec![
                checked_get,
                caller(
                    vec![
                        Inst::Call {
                            dest: 0,
                            func: 0,
                            args: vec![int(4)],
                            unwind: None,
                        },
                        Inst::Copy {
                            dest: 1,
                            src: local(0),
                        },
                    ],
                    local(1),
                ),
            ],
            entry: 1,
            global_slots: 0,
        };
        inline_small(&mut program);
        let function = &program.functions[1];
        assert!(
            !function
                .blocks
                .iter()
                .flat_map(|block| &block.insts)
                .any(|inst| matches!(inst, Inst::Call { .. })),
            "branching body was not inlined"
        );
        assert!(
            function
                .blocks
                .iter()
                .any(|block| matches!(block.term, Some(Term::Trap(_)))),
            "trap block missing after splice"
        );
        // The caller's tail (the Copy into local 1) still runs.
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| &block.insts)
                .any(|inst| matches!(inst, Inst::Copy { dest: 1, .. })),
            "caller tail lost in the split"
        );
    }

    #[test]
    fn param_writing_bodies_stay_calls() {
        let mut program = Program {
            functions: vec![
                Function {
                    name: "clobber".into(),
                    arity: 1,
                    n_locals: 1,
                    blocks: vec![BlockData {
                        params: Vec::new(),
                        insts: vec![Inst::Copy {
                            dest: 0,
                            src: int(9),
                        }],
                        term: Some(Term::Return(local(0))),
                    }],
                },
                caller(
                    vec![Inst::Call {
                        dest: 0,
                        func: 0,
                        args: vec![int(1)],
                        unwind: None,
                    }],
                    local(0),
                ),
            ],
            entry: 1,
            global_slots: 0,
        };
        inline_small(&mut program);
        assert!(
            program.functions[1].blocks[0]
                .insts
                .iter()
                .any(|inst| matches!(inst, Inst::Call { .. })),
            "param-writing body was inlined"
        );
    }

    #[test]
    fn callee_temporaries_get_fresh_caller_locals() {
        // add(t, 3) where t is caller local 1: the callee's temp must not
        // collide with existing caller locals.
        let mut program = Program {
            functions: vec![
                scalar_add(),
                caller(
                    vec![
                        Inst::Copy {
                            dest: 1,
                            src: int(40),
                        },
                        Inst::Call {
                            dest: 0,
                            func: 0,
                            args: vec![local(1), int(3)],
                            unwind: None,
                        },
                    ],
                    local(0),
                ),
            ],
            entry: 1,
            global_slots: 0,
        };
        inline_small(&mut program);
        let function = &program.functions[1];
        let insts = &function.blocks[0].insts;
        let Some(Inst::Scalar { dest, .. }) = insts
            .iter()
            .find(|inst| matches!(inst, Inst::Scalar { .. }))
        else {
            panic!("no scalar spliced: {insts:?}");
        };
        assert!(*dest >= 2, "callee temp reused a caller local");
        assert!(function.n_locals > 2, "caller frame not widened");
    }
}
