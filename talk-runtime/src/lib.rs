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
pub mod symbol;

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
    RecordNew {
        dest: u16,
        symbol: symbol::Symbol,
        args_start: u32,
        args_len: u16,
    },
    GetField {
        dest: u16,
        rec: u16,
        index: u16,
    },
    VariantNew {
        dest: u16,
        symbol: symbol::Symbol,
        tag: u16,
        args_start: u32,
        args_len: u16,
    },
    GetTag {
        dest: u16,
        src: u16,
    },
    GetPayload {
        dest: u16,
        src: u16,
        index: u16,
    },
    ExistentialPack {
        dest: u16,
        protocol: symbol::Symbol,
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
    TupleNew {
        dest: u16,
        args_start: u32,
        args_len: u16,
    },
    Extract {
        dest: u16,
        src: u16,
        index: u16,
    },
    SetField {
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

#[derive(Debug, Default)]
pub struct Module {
    pub chunks: Vec<Chunk>,
    pub consts: Vec<interp::Value>,
    pub arg_pool: Vec<u16>,
    pub switch_pool: Vec<u32>,
    pub traps: Vec<String>,
    pub statics: Vec<u8>,
    pub entry: u32,
}

impl Module {
    pub fn render(&self) -> String {
        self.render_styled(&Styles::plain())
    }

    pub fn render_ansi(&self) -> String {
        self.render_styled(&Styles::ansi())
    }

    pub fn render_styled(&self, s: &Styles) -> String {
        let mut out = String::new();
        for (i, chunk) in self.chunks.iter().enumerate() {
            out.push_str(&format!(
                "chunk {i}: {}{}{} (arity {}, regs {})\n",
                s.func, chunk.name, s.reset, chunk.arity, chunk.n_regs
            ));
            for (pc, insn) in chunk.code.iter().enumerate() {
                let text = self.render_insn(insn);
                let styled = match text.split_once(' ') {
                    Some((mnemonic, rest)) => {
                        format!("{}{mnemonic}{} {rest}", s.keyword, s.reset)
                    }
                    None => format!("{}{text}{}", s.keyword, s.reset),
                };
                out.push_str(&format!("  {pc}: {styled}\n"));
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
            Insn::Add { dest, a, b } => format!("add r{dest} <- r{a}, r{b}"),
            Insn::Sub { dest, a, b } => format!("sub r{dest} <- r{a}, r{b}"),
            Insn::Mul { dest, a, b } => format!("mul r{dest} <- r{a}, r{b}"),
            Insn::Div { dest, a, b } => format!("div r{dest} <- r{a}, r{b}"),
            Insn::Cmp { dest, a, b, op } => {
                format!(
                    "cmp_{} r{dest} <- r{a}, r{b}",
                    format!("{op:?}").to_lowercase()
                )
            }
            Insn::Trunc { dest, src } => format!("trunc r{dest} <- r{src}"),
            Insn::IToF { dest, src } => format!("itof r{dest} <- r{src}"),
            Insn::BToI { dest, src } => format!("btoi r{dest} <- r{src}"),
            Insn::CellNew { dest, init } => format!("cell_new r{dest} <- r{init}"),
            Insn::CellGet { dest, cell } => format!("cell_get r{dest} <- r{cell}"),
            Insn::CellSet { cell, src } => format!("cell_set r{cell} <- r{src}"),
            Insn::RecordNew {
                dest,
                symbol,
                args_start,
                args_len,
            } => format!(
                "record_new r{dest} <- {symbol}({})",
                self.render_args(*args_start, *args_len)
            ),
            Insn::GetField { dest, rec, index } => format!("get_field r{dest} <- r{rec}.{index}"),
            Insn::VariantNew {
                dest,
                symbol,
                tag,
                args_start,
                args_len,
            } => format!(
                "variant_new r{dest} <- {symbol}#{tag}({})",
                self.render_args(*args_start, *args_len)
            ),
            Insn::GetTag { dest, src } => format!("get_tag r{dest} <- r{src}"),
            Insn::GetPayload { dest, src, index } => {
                format!("get_payload r{dest} <- r{src}.{index}")
            }
            Insn::ExistentialPack {
                dest,
                protocol,
                args_start,
                args_len,
            } => format!(
                "existential_pack r{dest} <- any {protocol}({})",
                self.render_args(*args_start, *args_len)
            ),
            Insn::ExistentialWitness { dest, src, index } => {
                format!("existential_witness r{dest} <- r{src}.{index}")
            }
            Insn::ExistentialPayload { dest, src } => {
                format!("existential_payload r{dest} <- r{src}")
            }
            Insn::TupleNew {
                dest,
                args_start,
                args_len,
            } => format!(
                "tuple r{dest} <- ({})",
                self.render_args(*args_start, *args_len)
            ),
            Insn::Extract { dest, src, index } => format!("extract r{dest} <- r{src}.{index}"),
            Insn::SetField {
                dest,
                rec,
                src,
                index,
            } => format!("set_field r{dest} <- r{rec} with .{index} = r{src}"),
            Insn::Alloc { dest, count } => format!("alloc r{dest} <- r{count} bytes"),
            Insn::Free { dest, ptr } => format!("free r{dest} <- r{ptr}"),
            Insn::Retain { dest, ptr } => format!("retain r{dest} <- r{ptr}"),
            Insn::IsUnique { dest, ptr } => format!("is_unique r{dest} <- r{ptr}"),
            Insn::Load { dest, ptr, kind } => format!(
                "load_{} r{dest} <- [r{ptr}]",
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
        }
    }
}

pub struct Styles {
    pub func: &'static str,
    pub keyword: &'static str,
    pub reset: &'static str,
}

impl Styles {
    pub fn plain() -> Self {
        Self {
            func: "",
            keyword: "",
            reset: "",
        }
    }

    pub fn ansi() -> Self {
        Self {
            func: "\x1b[1;33m",
            keyword: "\x1b[1;35m",
            reset: "\x1b[0m",
        }
    }
}
