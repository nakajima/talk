#![cfg_attr(not(test), deny(clippy::unwrap_used))]
#![cfg_attr(not(test), deny(clippy::expect_used))]
#![cfg_attr(not(test), deny(clippy::panic))]
#![cfg_attr(not(test), deny(clippy::todo))]
#![allow(clippy::uninlined_format_args)]

pub mod bytecode;
pub mod interp;
pub mod io;
pub mod memory;
pub mod objects;
mod profile;
pub mod stats;
pub mod symbol;

pub use stats::{VmChunkStats, VmInstructionStats, VmOpcodeStats, VmStats};

/// VM-owned comparison operation. The compiler translates lambda-G
/// comparison primops into this runtime opcode during scheduling.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// What one memory access moves: a byte, a little-endian scalar word, or
/// an 8-byte handle into the boxed arena.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MemKind {
    Byte,
    I64,
    F64,
    Bool,
    Ptr,
    Boxed,
}

/// Sentinel layout id on `Field`/`SetField`/`GetElement`: the accessed
/// member is a single slot, not a spliced inline child. Any other value
/// is the spliced child's layout id.
pub const NO_LAYOUT: u32 = u32::MAX;

/// The member shape a `Field`/`SetField`/`GetElement` layout operand
/// encodes: `NO_LAYOUT` is one slot, anything else the spliced child.
pub fn member_shape(layout: u32) -> FieldShape {
    if layout == NO_LAYOUT {
        FieldShape::Slot
    } else {
        FieldShape::Spliced(layout)
    }
}

/// How one product field or sum payload element occupies its slots
/// (ADR 0045): one slot holding one value, or a nested inline aggregate
/// spliced flat across the child layout's width.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FieldShape {
    Slot,
    Spliced(u32),
}

/// The flat body of one published layout. Offsets index the aggregate's
/// slot vector; a sum's tag lives at slot 0 and payloads start at 1.
#[derive(Clone, Debug, PartialEq)]
pub enum LayoutBody {
    /// One (offset, shape) per field in declaration order.
    Product(Vec<(u16, FieldShape)>),
    /// Per variant in tag order, one (offset, shape) per payload element.
    Sum(Vec<Vec<(u16, FieldShape)>>),
    /// An id the table carries only to keep indices aligned (scalars,
    /// references, check-only entries): never constructed flat.
    Unshaped,
}

/// One published aggregate layout (ADR 0045): the shape of a flat
/// `Value::Agg` with this id. MIR computes these; the VM only reads them.
#[derive(Clone, Debug, PartialEq)]
pub struct LayoutDesc {
    /// Display identity for rendering (`None` for tuples, closed records,
    /// and inline arrays).
    pub symbol: Option<symbol::Symbol>,
    /// Total width in slots.
    pub width: u16,
    pub body: LayoutBody,
}

/// Register-or-constant operand encoding (Lua 5's RK design —
/// Ierusalimschy, de Figueiredo & Celes, *The Implementation of
/// Lua 5.0*, J.UCS 2005): when the high bit of an operand field is
/// set, the low 15 bits index the module constant pool; otherwise
/// the field is a frame register. RK fields are the arithmetic and
/// comparison operands (`Add`/`Sub`/`Mul`/`Div`/`Cmp` `a`/`b`) and
/// every argument-pool entry — a constant argument or operand costs
/// no materializing instruction. Constant pool indexes past 15 bits
/// fall back to `Const` materialization at lowering.
pub const RK_CONST: u16 = 0x8000;
/// The index mask under [`RK_CONST`].
pub const RK_INDEX: u16 = 0x7FFF;

/// Render an RK operand field the way the disassembly reads.
pub fn rk_display(field: u16) -> String {
    if field & RK_CONST != 0 {
        format!("k[{}]", field & RK_INDEX)
    } else {
        format!("r{field}")
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Insn {
    Const {
        dest: u16,
        k: u32,
    },
    Move {
        dest: u16,
        src: u16,
    },
    Add {
        dest: u16,
        a: u16,
        b: u16,
    },
    Sub {
        dest: u16,
        a: u16,
        b: u16,
    },
    Mul {
        dest: u16,
        a: u16,
        b: u16,
    },
    Div {
        dest: u16,
        a: u16,
        b: u16,
    },
    And {
        dest: u16,
        a: u16,
        b: u16,
    },
    Or {
        dest: u16,
        a: u16,
        b: u16,
    },
    Xor {
        dest: u16,
        a: u16,
        b: u16,
    },
    Shl {
        dest: u16,
        a: u16,
        b: u16,
    },
    Shr {
        dest: u16,
        a: u16,
        b: u16,
    },
    Not {
        dest: u16,
        src: u16,
    },
    Cmp {
        dest: u16,
        a: u16,
        b: u16,
        op: CmpOp,
    },
    Trunc {
        dest: u16,
        src: u16,
    },
    IToF {
        dest: u16,
        src: u16,
    },
    BToI {
        dest: u16,
        src: u16,
    },
    IToB {
        dest: u16,
        src: u16,
    },
    CellNew {
        dest: u16,
        init: u16,
    },
    CellGet {
        dest: u16,
        cell: u16,
    },
    CellSet {
        cell: u16,
        src: u16,
    },
    /// Build one flat aggregate ([`interp::Value::Agg`]) — struct, tuple,
    /// record, or enum variant — under a published layout. `tag` stamps
    /// slot 0 for sums and must be 0 for products; identity and shape
    /// both live in the layout table, never on the value.
    AggNew {
        dest: u16,
        layout: u32,
        tag: u16,
        args_start: u32,
        args_len: u16,
    },
    /// Offset-addressed field read on a flat aggregate (ADR 0045): the
    /// lowering resolved the logical index against the container's
    /// published layout. `layout` is [`NO_LAYOUT`] for a one-slot field,
    /// or the spliced child's layout id (the read reconstitutes that
    /// aggregate from its span).
    Field {
        dest: u16,
        src: u16,
        offset: u16,
        layout: u32,
    },
    /// Logical-index read through the value's own published layout —
    /// the existential boundary's read, where an element's width is
    /// dynamic at the site (a `mut` requirement's writeback tuple).
    /// Every statically-shaped container uses `Field` instead.
    FieldIndex {
        dest: u16,
        src: u16,
        index: u16,
    },
    /// Read one element of a flat aggregate at a runtime-validated
    /// dynamic index: the slot offset is `index` times the element's
    /// stride ([`NO_LAYOUT`] element = one slot; a spliced element's
    /// stride is its layout's width).
    GetElement {
        dest: u16,
        rec: u16,
        index: u16,
        element: u32,
    },
    GetTag {
        dest: u16,
        src: u16,
    },
    ExistentialPack {
        dest: u16,
        args_start: u32,
        args_len: u16,
    },
    ExistentialWitness {
        dest: u16,
        src: u16,
        index: u16,
    },
    ExistentialPayload {
        dest: u16,
        src: u16,
    },
    /// Offset-addressed field write (copy-on-write, value semantics):
    /// the flat counterpart of `Field`.
    SetField {
        dest: u16,
        rec: u16,
        src: u16,
        offset: u16,
        layout: u32,
    },
    /// Logical-index write through the value's own published layout —
    /// `FieldIndex`'s copy-on-write counterpart at the existential
    /// boundary.
    SetFieldIndex {
        dest: u16,
        rec: u16,
        src: u16,
        index: u16,
    },
    Alloc {
        dest: u16,
        count: u16,
    },
    Free {
        dest: u16,
        ptr: u16,
    },
    Retain {
        dest: u16,
        ptr: u16,
    },
    IsUnique {
        dest: u16,
        ptr: u16,
    },
    Load {
        dest: u16,
        ptr: u16,
        kind: MemKind,
    },
    /// Bounds-check and load one fixed-width memory element. An invalid
    /// index jumps to `failure_target`, where compiled Talk code owns the
    /// catchable failure behavior; this instruction never turns it into a
    /// VM trap.
    CheckedIndexedLoad {
        dest: u16,
        base: u16,
        index: u16,
        length: u16,
        kind: MemKind,
        failure_target: u32,
    },
    Store {
        ptr: u16,
        src: u16,
        kind: MemKind,
    },
    Copy {
        from: u16,
        to: u16,
        len: u16,
    },
    Swap {
        a: u16,
        b: u16,
        kind: MemKind,
    },
    Io {
        dest: u16,
        op: IoOp,
        a: u16,
        b: u16,
        c: u16,
    },
    Call {
        dest: u16,
        chunk: u32,
        args_start: u32,
        args_len: u16,
    },
    MakeClosure {
        dest: u16,
        chunk: u32,
        args_start: u32,
        args_len: u16,
    },
    EnvGet {
        dest: u16,
        index: u16,
    },
    CallIndirect {
        dest: u16,
        callee: u16,
        args_start: u32,
        args_len: u16,
    },
    Jump {
        target: u32,
    },
    Branch {
        cond: u16,
        then_target: u32,
        else_target: u32,
    },
    Switch {
        tag: u16,
        targets_start: u32,
        targets_len: u16,
    },
    Ret {
        src: u16,
    },
    ObjectNew {
        dest: u16,
        args_start: u32,
        args_len: u16,
    },
    SetFinalizer {
        obj: u16,
        closure: u16,
    },
    ObjectGet {
        dest: u16,
        obj: u16,
        index: u16,
    },
    ObjectSet {
        obj: u16,
        src: u16,
        index: u16,
    },
    RegionAcquire {
        dest: u16,
        src: u16,
    },
    RegionRelease {
        dest: u16,
        src: u16,
    },
    /// Reify the current frame's return continuation as a one-shot
    /// first-class value (the minimal M9 slice: effect-handler
    /// delimiters). Invoking it behaves as if this frame executed `Ret`.
    MakeCont {
        dest: u16,
    },
    /// Invoke a reified continuation with a value: unwind every frame
    /// above the continuation's frame — entering each one a final time at
    /// its unwind entry when its chunk's unwind table has one for the
    /// suspension pc (ADR 0027) — then return from that frame with the
    /// value. Traps if the frame is gone — continuations are one-shot,
    /// and a handler that escapes its scope finds a dead delimiter.
    CallCont {
        callee: u16,
        src: u16,
    },
    /// Terminates an unwind entry (ADR 0027): pop the frame that just ran
    /// its cleanup and continue the unwind toward the delimiter. Only
    /// legal while a `CallCont` unwind is in progress.
    UnwindRet,
    /// Install a deep handler for `effect`: the clause function value and
    /// the delimiter continuation, tied to the installing frame (popped
    /// with it).
    PushHandler {
        effect: u32,
        clause: u16,
        cont: u16,
    },
    /// Nearest-handler routing: find the innermost live handler for
    /// `effect` below the current search floor. Writes the clause, the
    /// delimiter continuation, and the handler's index (for the clause's
    /// own floor). Traps if no handler is installed.
    FindHandler {
        clause: u16,
        cont: u16,
        index: u16,
        effect: u32,
    },
    /// Read the current handler-search floor (an Int; `i64::MAX` = open).
    GetFloor {
        dest: u16,
    },
    /// Set the handler-search floor (a clause runs outside its own
    /// handler, CHG-01).
    SetFloor {
        src: u16,
    },
    Trap {
        message: u32,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoOp {
    Read,
    Write,
    Open,
    Close,
    Sleep,
    Poll,
    Ctl,
    Socket,
    Bind,
    Listen,
    Connect,
    Accept,
    CwdLen,
    CwdCopy,
    GetenvLen,
    GetenvCopy,
    Argc,
    ArgLen,
    ArgCopy,
    DirCount,
    DirEntryKind,
    DirEntryLen,
    DirEntryCopy,
    Exit,
    RealpathLen,
    RealpathCopy,
    Seek,
    FileSize,
}

impl IoOp {
    /// Every operation, in declaration order. This order is the wire
    /// format: core's `IORequest` variant order, the bytecode encoding,
    /// and the runtime operation table all index into it.
    pub const ALL: [IoOp; 28] = [
        IoOp::Read,
        IoOp::Write,
        IoOp::Open,
        IoOp::Close,
        IoOp::Sleep,
        IoOp::Poll,
        IoOp::Ctl,
        IoOp::Socket,
        IoOp::Bind,
        IoOp::Listen,
        IoOp::Connect,
        IoOp::Accept,
        IoOp::CwdLen,
        IoOp::CwdCopy,
        IoOp::GetenvLen,
        IoOp::GetenvCopy,
        IoOp::Argc,
        IoOp::ArgLen,
        IoOp::ArgCopy,
        IoOp::DirCount,
        IoOp::DirEntryKind,
        IoOp::DirEntryLen,
        IoOp::DirEntryCopy,
        IoOp::Exit,
        IoOp::RealpathLen,
        IoOp::RealpathCopy,
        IoOp::Seek,
        IoOp::FileSize,
    ];

    pub fn from_index(index: u8) -> Option<IoOp> {
        Self::ALL.get(usize::from(index)).copied()
    }

    pub fn index(self) -> u8 {
        self as u8
    }
}

#[derive(Debug)]
pub struct Chunk {
    pub name: String,
    pub code: Vec<Insn>,
    pub arity: u16,
    pub n_regs: u16,
    /// The unwind table (ADR 0027): (suspension pc, entry pc) pairs,
    /// sorted by suspension pc. A frame of this chunk suspended at a
    /// capability-passing call holds the suspension pc; an effect abort
    /// unwinding through it enters the frame once at the entry pc (the
    /// site's scope-exit drops, ending in `UnwindRet`) before popping it.
    pub unwind: Vec<(u32, u32)>,
}

/// Scalar value stored in a module's immutable constant pool.
///
/// Runtime aggregates use `Rc` for cheap local copies, but bytecode constants
/// are scalar-only. Keeping that invariant in the type makes [`Module`]
/// shareable across threads without imposing atomic reference counting on VM
/// values.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Constant {
    I64(i64),
    F64(f64),
    Bool(bool),
    Byte(u8),
    Void,
    Ptr(u32),
}

#[derive(Debug, Default)]
pub struct Module {
    pub chunks: Vec<Chunk>,
    pub consts: Vec<Constant>,
    pub arg_pool: Vec<u16>,
    pub switch_pool: Vec<u32>,
    pub traps: Vec<String>,
    pub statics: Vec<u8>,
    /// The published aggregate layouts (ADR 0045), indexed by the layout
    /// ids instructions carry.
    pub layouts: Vec<LayoutDesc>,
    pub entry: u32,
    /// Host-callable entry points: export name → wrapper chunk index.
    /// Unlike chunk names (diagnostic strings), these are an ABI: the
    /// host dispatches `interp::run_export` through this table.
    pub exports: Vec<(String, u32)>,
}

impl Module {
    pub fn render(&self) -> String {
        let mut out = String::new();
        for (i, chunk) in self.chunks.iter().enumerate() {
            out.push_str(&format!(
                "chunk {i}: {} (arity {}, regs {})\n",
                chunk.name, chunk.arity, chunk.n_regs
            ));
            for (pc, insn) in chunk.code.iter().enumerate() {
                out.push_str(&format!("  {pc}: {}\n", self.render_insn(insn)));
            }
        }
        out
    }

    fn render_args(&self, start: u32, len: u16) -> String {
        self.arg_pool[start as usize..start as usize + len as usize]
            .iter()
            .map(|r| format!("r{r}"))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn render_insn(&self, insn: &Insn) -> String {
        match insn {
            Insn::Const { dest, k } => format!("const r{dest} <- consts[{k}]"),
            Insn::Move { dest, src } => format!("move r{dest} <- r{src}"),
            Insn::Add { dest, a, b } => {
                format!("add r{dest} <- {}, {}", rk_display(*a), rk_display(*b))
            }
            Insn::Sub { dest, a, b } => {
                format!("sub r{dest} <- {}, {}", rk_display(*a), rk_display(*b))
            }
            Insn::Mul { dest, a, b } => {
                format!("mul r{dest} <- {}, {}", rk_display(*a), rk_display(*b))
            }
            Insn::Div { dest, a, b } => {
                format!("div r{dest} <- {}, {}", rk_display(*a), rk_display(*b))
            }
            Insn::And { dest, a, b } => {
                format!("and r{dest} <- {}, {}", rk_display(*a), rk_display(*b))
            }
            Insn::Or { dest, a, b } => {
                format!("or r{dest} <- {}, {}", rk_display(*a), rk_display(*b))
            }
            Insn::Xor { dest, a, b } => {
                format!("xor r{dest} <- {}, {}", rk_display(*a), rk_display(*b))
            }
            Insn::Shl { dest, a, b } => {
                format!("shl r{dest} <- {}, {}", rk_display(*a), rk_display(*b))
            }
            Insn::Shr { dest, a, b } => {
                format!("shr r{dest} <- {}, {}", rk_display(*a), rk_display(*b))
            }
            Insn::Not { dest, src } => format!("not r{dest} <- r{src}"),
            Insn::Cmp { dest, a, b, op } => {
                format!(
                    "cmp_{} r{dest} <- {}, {}",
                    format!("{op:?}").to_lowercase(),
                    rk_display(*a),
                    rk_display(*b)
                )
            }
            Insn::Trunc { dest, src } => format!("trunc r{dest} <- r{src}"),
            Insn::IToF { dest, src } => format!("itof r{dest} <- r{src}"),
            Insn::BToI { dest, src } => format!("btoi r{dest} <- r{src}"),
            Insn::IToB { dest, src } => format!("itob r{dest} <- r{src}"),
            Insn::CellNew { dest, init } => format!("cell_new r{dest} <- r{init}"),
            Insn::CellGet { dest, cell } => format!("cell_get r{dest} <- r{cell}"),
            Insn::CellSet { cell, src } => format!("cell_set r{cell} <- r{src}"),
            Insn::AggNew {
                dest,
                layout,
                tag,
                args_start,
                args_len,
            } => format!(
                "agg_new r{dest} <- L{layout}#{tag}({})",
                self.render_args(*args_start, *args_len)
            ),
            Insn::Field {
                dest,
                src,
                offset,
                layout,
            } => format!(
                "field r{dest} <- r{src}[{offset}]{}",
                layout_display(*layout)
            ),
            Insn::FieldIndex { dest, src, index } => {
                format!("field_index r{dest} <- r{src}.{index}")
            }
            Insn::GetElement {
                dest,
                rec,
                index,
                element,
            } => format!(
                "get_element r{dest} <- r{rec}[r{index}]{}",
                layout_display(*element)
            ),
            Insn::GetTag { dest, src } => format!("get_tag r{dest} <- r{src}"),
            Insn::ExistentialPack {
                dest,
                args_start,
                args_len,
            } => format!(
                "existential_pack r{dest} <- any({})",
                self.render_args(*args_start, *args_len)
            ),
            Insn::ExistentialWitness { dest, src, index } => {
                format!("existential_witness r{dest} <- r{src}.{index}")
            }
            Insn::ExistentialPayload { dest, src } => {
                format!("existential_payload r{dest} <- r{src}")
            }
            Insn::SetField {
                dest,
                rec,
                src,
                offset,
                layout,
            } => format!(
                "set_field r{dest} <- r{rec} with [{offset}]{} = r{src}",
                layout_display(*layout)
            ),
            Insn::SetFieldIndex {
                dest,
                rec,
                src,
                index,
            } => format!("set_field_index r{dest} <- r{rec} with .{index} = r{src}"),
            Insn::Alloc { dest, count } => format!("alloc r{dest} <- r{count} bytes"),
            Insn::Free { dest, ptr } => format!("free r{dest} <- r{ptr}"),
            Insn::Retain { dest, ptr } => format!("retain r{dest} <- r{ptr}"),
            Insn::IsUnique { dest, ptr } => format!("is_unique r{dest} <- r{ptr}"),
            Insn::Load { dest, ptr, kind } => format!(
                "load_{} r{dest} <- [r{ptr}]",
                format!("{kind:?}").to_lowercase()
            ),
            Insn::CheckedIndexedLoad {
                dest,
                base,
                index,
                length,
                kind,
                failure_target,
            } => format!(
                "checked_indexed_load_{} r{dest} <- [r{base} + r{index}], len r{length}, fail {failure_target}",
                format!("{kind:?}").to_lowercase()
            ),
            Insn::Store { ptr, src, kind } => format!(
                "store_{} [r{ptr}] <- r{src}",
                format!("{kind:?}").to_lowercase()
            ),
            Insn::Copy { from, to, len } => format!("copy [r{to}] <- [r{from}], r{len} bytes"),
            Insn::Swap { a, b, kind } => {
                format!("swap_{} [r{a}], [r{b}]", format!("{kind:?}").to_lowercase())
            }
            Insn::Io { dest, op, a, b, c } => format!(
                "io_{} r{dest} <- r{a}, r{b}, r{c}",
                format!("{op:?}").to_lowercase()
            ),
            Insn::Call {
                dest,
                chunk,
                args_start,
                args_len,
            } => format!(
                "call r{dest} <- {}({})",
                self.chunks[*chunk as usize].name,
                self.render_args(*args_start, *args_len)
            ),
            Insn::MakeClosure {
                dest,
                chunk,
                args_start,
                args_len,
            } => format!(
                "closure r{dest} <- {} capturing ({})",
                self.chunks[*chunk as usize].name,
                self.render_args(*args_start, *args_len)
            ),
            Insn::EnvGet { dest, index } => format!("env_get r{dest} <- env[{index}]"),
            Insn::CallIndirect {
                dest,
                callee,
                args_start,
                args_len,
            } => format!(
                "call_indirect r{dest} <- r{callee}({})",
                self.render_args(*args_start, *args_len)
            ),
            Insn::Jump { target } => format!("jump {target}"),
            Insn::Branch {
                cond,
                then_target,
                else_target,
            } => format!("branch r{cond} ? {then_target} : {else_target}"),
            Insn::Switch {
                tag,
                targets_start,
                targets_len,
            } => {
                let targets = &self.switch_pool
                    [*targets_start as usize..*targets_start as usize + *targets_len as usize];
                let (default, arms) = targets.split_last().unwrap_or((&0, &[]));
                let arms: Vec<String> = arms.iter().map(|t| t.to_string()).collect();
                format!("switch r{tag} -> [{}] default {default}", arms.join(", "))
            }
            Insn::Ret { src } => format!("ret r{src}"),
            Insn::Trap { message } => format!("trap {:?}", self.traps[*message as usize]),
            Insn::ObjectNew {
                dest,
                args_start,
                args_len,
            } => format!(
                "object_new r{dest} <- {}",
                self.render_args(*args_start, *args_len)
            ),
            Insn::SetFinalizer { obj, closure } => format!("set_finalizer r{obj} <- r{closure}"),
            Insn::ObjectGet { dest, obj, index } => {
                format!("object_get r{dest} <- r{obj}[{index}]")
            }
            Insn::ObjectSet { obj, src, index } => format!("object_set r{obj}[{index}] <- r{src}"),
            Insn::RegionAcquire { dest, src } => format!("region_acquire r{dest} <- r{src}"),
            Insn::RegionRelease { dest, src } => format!("region_release r{dest} <- r{src}"),
            Insn::MakeCont { dest } => format!("make_cont r{dest}"),
            Insn::CallCont { callee, src } => format!("call_cont r{callee} <- r{src}"),
            Insn::UnwindRet => "unwind_ret".to_string(),
            Insn::PushHandler {
                effect,
                clause,
                cont,
            } => {
                format!("push_handler eff{effect} clause r{clause} cont r{cont}")
            }
            Insn::FindHandler {
                clause,
                cont,
                index,
                effect,
            } => {
                format!("find_handler eff{effect} -> r{clause}, r{cont}, r{index}")
            }
            Insn::GetFloor { dest } => format!("get_floor r{dest}"),
            Insn::SetFloor { src } => format!("set_floor r{src}"),
        }
    }
}

/// Layout suffix for disassembly: nothing for [`NO_LAYOUT`].
fn layout_display(layout: u32) -> String {
    if layout == NO_LAYOUT {
        String::new()
    } else {
        format!("@L{layout}")
    }
}
