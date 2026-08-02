//! Projection from private compiler MIR to the public code-generation model.
//!
//! This boundary is exhaustive so a new MIR operation must acquire a deliberate
//! external representation before the compiler builds again.

use super::ProgramInput;
use super::mir as source;
use crate::name_resolution::symbol::Symbol;

pub(crate) fn project(
    program: &source::Program,
    programs: &[ProgramInput<'_>],
) -> crate::codegen::Compilation<Symbol> {
    crate::codegen::Compilation {
        program: Projection::program(program),
        display_names: Projection::display_names(programs),
        string_symbol: Symbol::String,
        storage_symbol: Symbol::Storage,
    }
}

struct Projection;

impl Projection {
    fn program(program: &source::Program) -> crate::codegen::Program<Symbol> {
        crate::codegen::Program {
            functions: program.functions.iter().map(Self::function).collect(),
            entry: program.entry,
            global_slots: program.global_slots,
            layouts: program.layout_table.iter().map(Self::layout).collect(),
        }
    }

    fn function(function: &source::Function) -> crate::codegen::Function<Symbol> {
        crate::codegen::Function {
            name: function.name.clone(),
            arity: function.arity,
            n_locals: function.n_locals(),
            blocks: function.blocks.iter().map(Self::block).collect(),
        }
    }

    fn block(block: &source::BlockData) -> crate::codegen::BlockData<Symbol> {
        crate::codegen::BlockData {
            params: block.params.clone(),
            insts: block.insts.iter().map(Self::inst).collect(),
            term: block.term.as_ref().map(Self::term),
        }
    }

    fn operand(operand: source::Operand) -> crate::codegen::Operand {
        match operand {
            source::Operand::Local(local) => crate::codegen::Operand::Local(local),
            source::Operand::Const(constant) => {
                crate::codegen::Operand::Const(Self::constant(constant))
            }
        }
    }

    fn constant(constant: source::Constant) -> crate::codegen::Constant {
        match constant {
            source::Constant::Unit => crate::codegen::Constant::Unit,
            source::Constant::Bool(value) => crate::codegen::Constant::Bool(value),
            source::Constant::Int(value) => crate::codegen::Constant::Int(value),
            source::Constant::Float(value) => crate::codegen::Constant::Float(value),
        }
    }

    fn comparison(kind: source::CmpKind) -> crate::codegen::CmpKind {
        match kind {
            source::CmpKind::Eq => crate::codegen::CmpKind::Eq,
            source::CmpKind::Ne => crate::codegen::CmpKind::Ne,
            source::CmpKind::Lt => crate::codegen::CmpKind::Lt,
            source::CmpKind::Le => crate::codegen::CmpKind::Le,
            source::CmpKind::Gt => crate::codegen::CmpKind::Gt,
            source::CmpKind::Ge => crate::codegen::CmpKind::Ge,
        }
    }

    fn scalar(op: source::ScalarOp) -> crate::codegen::ScalarOp {
        match op {
            source::ScalarOp::IntAdd => crate::codegen::ScalarOp::IntAdd,
            source::ScalarOp::IntSub => crate::codegen::ScalarOp::IntSub,
            source::ScalarOp::IntMul => crate::codegen::ScalarOp::IntMul,
            source::ScalarOp::IntDiv => crate::codegen::ScalarOp::IntDiv,
            source::ScalarOp::FloatAdd => crate::codegen::ScalarOp::FloatAdd,
            source::ScalarOp::FloatSub => crate::codegen::ScalarOp::FloatSub,
            source::ScalarOp::FloatMul => crate::codegen::ScalarOp::FloatMul,
            source::ScalarOp::FloatDiv => crate::codegen::ScalarOp::FloatDiv,
            source::ScalarOp::IntAnd => crate::codegen::ScalarOp::IntAnd,
            source::ScalarOp::IntOr => crate::codegen::ScalarOp::IntOr,
            source::ScalarOp::IntXor => crate::codegen::ScalarOp::IntXor,
            source::ScalarOp::IntShl => crate::codegen::ScalarOp::IntShl,
            source::ScalarOp::IntShr => crate::codegen::ScalarOp::IntShr,
            source::ScalarOp::IntNot => crate::codegen::ScalarOp::IntNot,
            source::ScalarOp::ByteAnd => crate::codegen::ScalarOp::ByteAnd,
            source::ScalarOp::ByteOr => crate::codegen::ScalarOp::ByteOr,
            source::ScalarOp::ByteXor => crate::codegen::ScalarOp::ByteXor,
            source::ScalarOp::ByteShl => crate::codegen::ScalarOp::ByteShl,
            source::ScalarOp::ByteShr => crate::codegen::ScalarOp::ByteShr,
            source::ScalarOp::ByteNot => crate::codegen::ScalarOp::ByteNot,
            source::ScalarOp::IntCmp(kind) => {
                crate::codegen::ScalarOp::IntCmp(Self::comparison(kind))
            }
            source::ScalarOp::FloatCmp(kind) => {
                crate::codegen::ScalarOp::FloatCmp(Self::comparison(kind))
            }
            source::ScalarOp::ByteCmp(kind) => {
                crate::codegen::ScalarOp::ByteCmp(Self::comparison(kind))
            }
            source::ScalarOp::BoolCmp(kind) => {
                crate::codegen::ScalarOp::BoolCmp(Self::comparison(kind))
            }
            source::ScalarOp::FloatToIntTrunc => crate::codegen::ScalarOp::FloatToIntTrunc,
            source::ScalarOp::IntToFloat => crate::codegen::ScalarOp::IntToFloat,
            source::ScalarOp::ByteToInt => crate::codegen::ScalarOp::ByteToInt,
            source::ScalarOp::IntToByte => crate::codegen::ScalarOp::IntToByte,
        }
    }

    fn slot_kind(kind: source::layout::SlotKind) -> crate::codegen::SlotKind {
        match kind {
            source::layout::SlotKind::Int => crate::codegen::SlotKind::Int,
            source::layout::SlotKind::Bool => crate::codegen::SlotKind::Bool,
            source::layout::SlotKind::Byte => crate::codegen::SlotKind::Byte,
            source::layout::SlotKind::F64 => crate::codegen::SlotKind::F64,
            source::layout::SlotKind::Ptr => crate::codegen::SlotKind::Ptr,
            source::layout::SlotKind::Value => crate::codegen::SlotKind::Value,
        }
    }

    fn field_repr(repr: source::layout::FieldRepr) -> crate::codegen::FieldRepr {
        match repr {
            source::layout::FieldRepr::Slot(kind) => {
                crate::codegen::FieldRepr::Slot(Self::slot_kind(kind))
            }
            source::layout::FieldRepr::Spliced(layout) => {
                crate::codegen::FieldRepr::Spliced(layout)
            }
        }
    }

    fn shape(shape: &source::layout::Shape) -> crate::codegen::Shape {
        match shape {
            source::layout::Shape::Product {
                width,
                offsets,
                reprs,
                kinds,
            } => crate::codegen::Shape::Product {
                width: *width,
                offsets: offsets.clone(),
                reprs: reprs.iter().copied().map(Self::field_repr).collect(),
                kinds: kinds.iter().copied().map(Self::slot_kind).collect(),
            },
            source::layout::Shape::Sum {
                width,
                payloads,
                reprs,
                kinds,
            } => crate::codegen::Shape::Sum {
                width: *width,
                payloads: payloads.clone(),
                reprs: reprs
                    .iter()
                    .map(|reprs| reprs.iter().copied().map(Self::field_repr).collect())
                    .collect(),
                kinds: kinds.iter().copied().map(Self::slot_kind).collect(),
            },
        }
    }

    fn layout(layout: &source::layout::Layout) -> crate::codegen::Layout<Symbol> {
        match layout {
            source::layout::Layout::Slot => crate::codegen::Layout::Slot,
            source::layout::Layout::Inline(symbol, shape) => {
                crate::codegen::Layout::Inline(*symbol, Self::shape(shape))
            }
            source::layout::Layout::Boxed(symbol, shape) => {
                crate::codegen::Layout::Boxed(*symbol, Self::shape(shape))
            }
            source::layout::Layout::Opaque => crate::codegen::Layout::Opaque,
        }
    }

    fn operands(operands: &[source::Operand]) -> Vec<crate::codegen::Operand> {
        operands.iter().copied().map(Self::operand).collect()
    }

    fn inst(inst: &source::Inst) -> crate::codegen::Inst<Symbol> {
        match inst {
            source::Inst::Copy { dest, src } => crate::codegen::Inst::Copy {
                dest: *dest,
                src: Self::operand(*src),
            },
            source::Inst::Scalar { dest, op, a, b } => crate::codegen::Inst::Scalar {
                dest: *dest,
                op: Self::scalar(*op),
                a: Self::operand(*a),
                b: b.map(Self::operand),
            },
            source::Inst::Call {
                dest,
                func,
                args,
                unwind,
            } => crate::codegen::Inst::Call {
                dest: *dest,
                func: *func,
                args: Self::operands(args),
                unwind: *unwind,
            },
            source::Inst::Aggregate {
                dest,
                tag,
                layout,
                args,
            } => crate::codegen::Inst::Aggregate {
                dest: *dest,
                tag: *tag,
                layout: *layout,
                args: Self::operands(args),
            },
            source::Inst::GetTag { dest, src } => crate::codegen::Inst::GetTag {
                dest: *dest,
                src: Self::operand(*src),
            },
            source::Inst::Blank { dest, layout } => crate::codegen::Inst::Blank {
                dest: *dest,
                layout: *layout,
            },
            source::Inst::Field {
                dest,
                src,
                container,
                offset,
                member,
            } => crate::codegen::Inst::Field {
                dest: *dest,
                src: Self::operand(*src),
                container: *container,
                offset: *offset,
                member: *member,
            },
            source::Inst::FieldIndex { dest, src, index } => crate::codegen::Inst::FieldIndex {
                dest: *dest,
                src: Self::operand(*src),
                index: *index,
            },
            source::Inst::GetElement {
                dest,
                src,
                element,
                index,
            } => crate::codegen::Inst::GetElement {
                dest: *dest,
                src: Self::operand(*src),
                element: *element,
                index: Self::operand(*index),
            },
            source::Inst::SetField {
                rec,
                src,
                container,
                offset,
                member,
            } => crate::codegen::Inst::SetField {
                rec: *rec,
                src: Self::operand(*src),
                container: *container,
                offset: *offset,
                member: *member,
            },
            source::Inst::SetFieldIndex { rec, src, index } => {
                crate::codegen::Inst::SetFieldIndex {
                    rec: *rec,
                    src: Self::operand(*src),
                    index: *index,
                }
            }
            source::Inst::StringLit {
                dest,
                bytes,
                layout,
                storage_layout,
            } => crate::codegen::Inst::StringLit {
                dest: *dest,
                bytes: bytes.clone(),
                layout: *layout,
                storage_layout: *storage_layout,
            },
            source::Inst::BytesLit { dest, bytes } => crate::codegen::Inst::BytesLit {
                dest: *dest,
                bytes: bytes.clone(),
            },
            source::Inst::Alloc { dest, bytes } => crate::codegen::Inst::Alloc {
                dest: *dest,
                bytes: Self::operand(*bytes),
            },
            source::Inst::Free { src } => crate::codegen::Inst::Free {
                src: Self::operand(*src),
            },
            source::Inst::RetainPtr { src } => crate::codegen::Inst::RetainPtr {
                src: Self::operand(*src),
            },
            source::Inst::IsUnique { dest, src } => crate::codegen::Inst::IsUnique {
                dest: *dest,
                src: Self::operand(*src),
            },
            source::Inst::Load { dest, ptr, kind } => crate::codegen::Inst::Load {
                dest: *dest,
                ptr: Self::operand(*ptr),
                kind: Self::slot_kind(*kind),
            },
            source::Inst::Store { ptr, src, kind } => crate::codegen::Inst::Store {
                ptr: Self::operand(*ptr),
                src: Self::operand(*src),
                kind: Self::slot_kind(*kind),
            },
            source::Inst::MemCopy { from, to, len } => crate::codegen::Inst::MemCopy {
                from: Self::operand(*from),
                to: Self::operand(*to),
                len: Self::operand(*len),
            },
            source::Inst::PtrAdd {
                dest,
                ptr,
                offset,
                size,
            } => crate::codegen::Inst::PtrAdd {
                dest: *dest,
                ptr: Self::operand(*ptr),
                offset: Self::operand(*offset),
                size: *size,
            },
            source::Inst::Io { dest, op, a, b, c } => crate::codegen::Inst::Io {
                dest: *dest,
                op: *op,
                a: Self::operand(*a),
                b: Self::operand(*b),
                c: Self::operand(*c),
            },
            source::Inst::ObjectNew { dest, args } => crate::codegen::Inst::ObjectNew {
                dest: *dest,
                args: Self::operands(args),
            },
            source::Inst::ObjectGet { dest, src, index } => crate::codegen::Inst::ObjectGet {
                dest: *dest,
                src: Self::operand(*src),
                index: *index,
            },
            source::Inst::ObjectSet { obj, src, index } => crate::codegen::Inst::ObjectSet {
                obj: Self::operand(*obj),
                src: Self::operand(*src),
                index: *index,
            },
            source::Inst::RegionAcquire { src } => crate::codegen::Inst::RegionAcquire {
                src: Self::operand(*src),
            },
            source::Inst::RegionRelease { src } => crate::codegen::Inst::RegionRelease {
                src: Self::operand(*src),
            },
            source::Inst::MakeClosure { dest, func, env } => crate::codegen::Inst::MakeClosure {
                dest: *dest,
                func: *func,
                env: Self::operands(env),
            },
            source::Inst::SetFinalizer { obj, closure } => crate::codegen::Inst::SetFinalizer {
                obj: Self::operand(*obj),
                closure: Self::operand(*closure),
            },
            source::Inst::CellNew { dest, init } => crate::codegen::Inst::CellNew {
                dest: *dest,
                init: Self::operand(*init),
            },
            source::Inst::CellGet { dest, cell } => crate::codegen::Inst::CellGet {
                dest: *dest,
                cell: Self::operand(*cell),
            },
            source::Inst::CellSet { cell, src } => crate::codegen::Inst::CellSet {
                cell: Self::operand(*cell),
                src: Self::operand(*src),
            },
            source::Inst::CallIndirect {
                dest,
                callee,
                args,
                unwind,
            } => crate::codegen::Inst::CallIndirect {
                dest: *dest,
                callee: Self::operand(*callee),
                args: Self::operands(args),
                unwind: *unwind,
            },
            source::Inst::EnvGet { dest, index } => crate::codegen::Inst::EnvGet {
                dest: *dest,
                index: *index,
            },
            source::Inst::MakeCont { dest } => crate::codegen::Inst::MakeCont { dest: *dest },
            source::Inst::PushHandler {
                effect,
                clause,
                cont,
            } => crate::codegen::Inst::PushHandler {
                effect: *effect,
                clause: Self::operand(*clause),
                cont: Self::operand(*cont),
            },
            source::Inst::FindHandler {
                clause,
                cont,
                index,
                effect,
            } => crate::codegen::Inst::FindHandler {
                clause: *clause,
                cont: *cont,
                index: *index,
                effect: *effect,
            },
            source::Inst::GetFloor { dest } => crate::codegen::Inst::GetFloor { dest: *dest },
            source::Inst::SetFloor { src } => crate::codegen::Inst::SetFloor {
                src: Self::operand(*src),
            },
            source::Inst::GlobalLoad { dest, global } => crate::codegen::Inst::GlobalLoad {
                dest: *dest,
                global: *global,
            },
            source::Inst::GlobalStore { global, src } => crate::codegen::Inst::GlobalStore {
                global: *global,
                src: Self::operand(*src),
            },
            source::Inst::ExistentialPack {
                dest,
                protocol,
                payload,
                witnesses,
            } => crate::codegen::Inst::ExistentialPack {
                dest: *dest,
                protocol: *protocol,
                payload: Self::operand(*payload),
                witnesses: Self::operands(witnesses),
            },
            source::Inst::ExistentialWitness { dest, src, index } => {
                crate::codegen::Inst::ExistentialWitness {
                    dest: *dest,
                    src: Self::operand(*src),
                    index: *index,
                }
            }
            source::Inst::ExistentialPayload { dest, src } => {
                crate::codegen::Inst::ExistentialPayload {
                    dest: *dest,
                    src: Self::operand(*src),
                }
            }
            source::Inst::AbortTo { cont, value } => crate::codegen::Inst::AbortTo {
                cont: Self::operand(*cont),
                value: Self::operand(*value),
            },
        }
    }

    fn term(term: &source::Term) -> crate::codegen::Term {
        match term {
            source::Term::Goto(target, args) => {
                crate::codegen::Term::Goto(*target, Self::operands(args))
            }
            source::Term::Branch {
                cond,
                then_block,
                else_block,
            } => crate::codegen::Term::Branch {
                cond: Self::operand(*cond),
                then_block: *then_block,
                else_block: *else_block,
            },
            source::Term::Switch {
                tag,
                targets,
                default,
            } => crate::codegen::Term::Switch {
                tag: Self::operand(*tag),
                targets: targets.clone(),
                default: *default,
            },
            source::Term::Return(value) => crate::codegen::Term::Return(Self::operand(*value)),
            source::Term::Trap(message) => crate::codegen::Term::Trap((*message).into()),
            source::Term::UnwindRet => crate::codegen::Term::UnwindRet,
        }
    }

    fn display_names(programs: &[ProgramInput<'_>]) -> crate::codegen::DisplayNames<Symbol> {
        let mut names = crate::codegen::DisplayNames::default();
        for input in programs {
            let types = input.program.types();
            let resolved = input.program.resolved_names();
            let name_of = |symbol: &Symbol| {
                resolved
                    .symbol_names
                    .get(symbol)
                    .cloned()
                    .unwrap_or_else(|| format!("{symbol:?}"))
            };
            for (symbol, def) in &types.catalog.enums {
                names.insert(
                    *symbol,
                    name_of(symbol),
                    crate::codegen::TypeKind::Enum,
                    def.variants.keys().cloned().collect(),
                );
            }
            for (symbol, def) in &types.catalog.structs {
                names.insert(
                    *symbol,
                    name_of(symbol),
                    if *symbol == Symbol::String {
                        crate::codegen::TypeKind::String
                    } else {
                        crate::codegen::TypeKind::Record
                    },
                    def.fields.keys().cloned().collect(),
                );
            }
        }
        names
    }
}
