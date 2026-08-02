use super::{Inst, LocalId, Operand, Term};

/// Which side of an instruction a local appears on.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Slot {
    Def,
    Use(Escape),
}

/// Whether a use hands the value to something that may outlive the
/// instruction — construction arguments, stores, call arguments, block
/// edges — or merely reads it in place. The escape analysis consumes
/// this; every other visitor treats both as a use.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Escape {
    No,
    May,
}

impl Slot {
    pub(crate) fn is_use(self) -> bool {
        matches!(self, Slot::Use(_))
    }
}

/// Visit every local in an instruction, mutably. Analysis and rewriting share
/// this exhaustive walk, so a new operand shape has one update point.
pub(crate) fn visit_inst(inst: &mut Inst, visit: &mut impl FnMut(Slot, &mut LocalId)) {
    let read = |op: &mut Operand, visit: &mut dyn FnMut(Slot, &mut LocalId)| {
        if let Operand::Local(local) = op {
            visit(Slot::Use(Escape::No), local);
        }
    };
    let sink = |op: &mut Operand, visit: &mut dyn FnMut(Slot, &mut LocalId)| {
        if let Operand::Local(local) = op {
            visit(Slot::Use(Escape::May), local);
        }
    };
    match inst {
        Inst::Copy { dest, src }
        | Inst::Field { dest, src, .. }
        | Inst::GetTag { dest, src }
        | Inst::IsUnique { dest, src }
        | Inst::ObjectGet { dest, src, .. }
        | Inst::ExistentialWitness { dest, src, .. }
        | Inst::ExistentialPayload { dest, src } => {
            read(src, visit);
            visit(Slot::Def, dest);
        }
        Inst::FieldIndex { dest, src, .. } => {
            read(src, visit);
            visit(Slot::Def, dest);
        }
        Inst::SetFieldIndex { rec, src, .. } => {
            visit(Slot::Use(Escape::No), rec);
            sink(src, visit);
        }
        Inst::GetElement {
            dest, src, index, ..
        } => {
            read(src, visit);
            read(index, visit);
            visit(Slot::Def, dest);
        }
        Inst::Scalar { dest, a, b, .. } => {
            read(a, visit);
            if let Some(b) = b {
                read(b, visit);
            }
            visit(Slot::Def, dest);
        }
        // Call arguments may escape through the callee; the escape walk
        // refines this per parameter with the callee's summary.
        Inst::Call { dest, args, .. }
        | Inst::Aggregate { dest, args, .. }
        | Inst::ObjectNew { dest, args } => {
            for arg in args {
                sink(arg, visit);
            }
            visit(Slot::Def, dest);
        }
        Inst::CallIndirect {
            dest, callee, args, ..
        } => {
            sink(callee, visit);
            for arg in args {
                sink(arg, visit);
            }
            visit(Slot::Def, dest);
        }
        Inst::SetField { rec, src, .. } => {
            visit(Slot::Use(Escape::No), rec);
            sink(src, visit);
        }
        Inst::StringLit { dest, .. }
        | Inst::Blank { dest, .. }
        | Inst::BytesLit { dest, .. }
        | Inst::EnvGet { dest, .. }
        | Inst::MakeCont { dest }
        | Inst::GetFloor { dest }
        | Inst::GlobalLoad { dest, .. } => visit(Slot::Def, dest),
        Inst::Alloc { dest, bytes } => {
            sink(bytes, visit);
            visit(Slot::Def, dest);
        }
        Inst::Free { src }
        | Inst::RetainPtr { src }
        | Inst::RegionAcquire { src }
        | Inst::RegionRelease { src }
        | Inst::SetFloor { src } => sink(src, visit),
        Inst::Load { dest, ptr, .. } => {
            read(ptr, visit);
            visit(Slot::Def, dest);
        }
        Inst::Store { ptr, src, .. } => {
            sink(ptr, visit);
            sink(src, visit);
        }
        Inst::MemCopy { from, to, len } => {
            sink(from, visit);
            sink(to, visit);
            sink(len, visit);
        }
        Inst::PtrAdd {
            dest, ptr, offset, ..
        } => {
            sink(ptr, visit);
            sink(offset, visit);
            visit(Slot::Def, dest);
        }
        Inst::Io { dest, a, b, c, .. } => {
            sink(a, visit);
            sink(b, visit);
            sink(c, visit);
            visit(Slot::Def, dest);
        }
        Inst::ObjectSet { obj, src, .. } => {
            read(obj, visit);
            sink(src, visit);
        }
        Inst::MakeClosure { dest, env, .. } => {
            for capture in env {
                sink(capture, visit);
            }
            visit(Slot::Def, dest);
        }
        Inst::SetFinalizer { obj, closure } => {
            sink(obj, visit);
            sink(closure, visit);
        }
        Inst::CellNew { dest, init } => {
            sink(init, visit);
            visit(Slot::Def, dest);
        }
        Inst::CellGet { dest, cell } => {
            read(cell, visit);
            visit(Slot::Def, dest);
        }
        Inst::CellSet { cell, src } => {
            read(cell, visit);
            sink(src, visit);
        }
        Inst::PushHandler { clause, cont, .. } => {
            sink(clause, visit);
            sink(cont, visit);
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
        Inst::GlobalStore { src, .. } => sink(src, visit),
        Inst::ExistentialPack {
            dest,
            payload,
            witnesses,
            ..
        } => {
            sink(payload, visit);
            for witness in witnesses {
                sink(witness, visit);
            }
            visit(Slot::Def, dest);
        }
        Inst::AbortTo { cont, value } => {
            sink(cont, visit);
            sink(value, visit);
        }
    }
}

pub(crate) fn visit_term(term: &mut Term, visit: &mut impl FnMut(Slot, &mut LocalId)) {
    match term {
        Term::Branch { cond: op, .. } | Term::Switch { tag: op, .. } => {
            if let Operand::Local(local) = op {
                visit(Slot::Use(Escape::No), local);
            }
        }
        // Returning hands the value to a frame that outlives this one; a
        // block argument can carry it across a back edge, where the
        // site's single storage slot would be reused.
        Term::Return(op) => {
            if let Operand::Local(local) = op {
                visit(Slot::Use(Escape::May), local);
            }
        }
        Term::Goto(_, edge_args) => {
            for arg in edge_args {
                if let Operand::Local(local) = arg {
                    visit(Slot::Use(Escape::May), local);
                }
            }
        }
        Term::Trap(_) | Term::UnwindRet => {}
    }
}
