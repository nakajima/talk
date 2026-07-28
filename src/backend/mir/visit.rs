use super::{Inst, LocalId, Operand, Term};

/// Which side of an instruction a local appears on.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Slot {
    Def,
    Use,
}

/// Visit every local in an instruction, mutably. Analysis and rewriting share
/// this exhaustive walk, so a new operand shape has one update point.
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
