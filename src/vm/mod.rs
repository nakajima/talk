//! The register bytecode machine: λ_G is scheduled (schedule.rs) into
//! chunks of register instructions and executed by a frame-stack
//! interpreter (interp.rs). Register bytecode per Shi, Casey, Ertl & Gregg,
//! *Virtual Machine Showdown* (VEE 2005) and Lua 5.0 (Ierusalimschy et al.,
//! J.UCS 2005); dispatch is a Rust `match` (Ertl & Gregg, JILP 2003 — the
//! threaded-code alternative is the known faster path if it ever matters).
//! Instructions are an unpacked fixed-shape enum with resolved jump targets
//! and pooled constants/argument lists — register-bytecode semantics; byte
//! packing is a later, mechanical optimization.

pub mod interp;
pub mod io;
pub mod schedule;

#[cfg(test)]
pub mod vm_tests;

use crate::lambda_g::expr::CmpOp;

/// What one memory access moves: a byte, a little-endian scalar word, or
/// an 8-byte handle into the boxed arena (aggregates never live in raw
/// memory directly — Leroy, POPL 1992's mixed representation).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MemKind {
    Byte,
    I64,
    F64,
    Bool,
    Ptr,
    Boxed,
}

impl MemKind {
    /// The memory access for a λ_G type, if it can live in raw memory.
    pub fn of(ty: &crate::lambda_g::expr::TyKind) -> Option<MemKind> {
        use crate::lambda_g::expr::TyKind;
        match ty {
            TyKind::Byte => Some(MemKind::Byte),
            TyKind::I64 => Some(MemKind::I64),
            TyKind::F64 => Some(MemKind::F64),
            TyKind::Bool => Some(MemKind::Bool),
            TyKind::Ptr => Some(MemKind::Ptr),
            TyKind::Boxed(_) | TyKind::Variant(_) | TyKind::Tuple(_) => Some(MemKind::Boxed),
            TyKind::Void | TyKind::Bot | TyKind::Fn(..) | TyKind::Cell(_) => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Insn {
    /// dest ← consts[k]
    Const { dest: u16, k: u32 },
    Move { dest: u16, src: u16 },
    Add { dest: u16, a: u16, b: u16 },
    Sub { dest: u16, a: u16, b: u16 },
    Mul { dest: u16, a: u16, b: u16 },
    Div { dest: u16, a: u16, b: u16 },
    Cmp { dest: u16, a: u16, b: u16, op: CmpOp },
    Trunc { dest: u16, src: u16 },
    IToF { dest: u16, src: u16 },
    CellNew { dest: u16, init: u16 },
    CellGet { dest: u16, cell: u16 },
    CellSet { cell: u16, src: u16 },
    /// dest ← fresh record with fields from the arg pool (registers).
    RecordNew {
        dest: u16,
        symbol: crate::name_resolution::symbol::Symbol,
        args_start: u32,
        args_len: u16,
    },
    GetField { dest: u16, rec: u16, index: u16 },
    /// dest ← fresh variant (enum value) with payloads from the arg pool.
    VariantNew {
        dest: u16,
        symbol: crate::name_resolution::symbol::Symbol,
        tag: u16,
        args_start: u32,
        args_len: u16,
    },
    /// dest ← the variant's tag, as an integer (feeds Switch).
    GetTag { dest: u16, src: u16 },
    /// dest ← payload `index` of the variant in src.
    GetPayload { dest: u16, src: u16, index: u16 },
    /// dest ← tuple of the arg-pool registers (kept boxed in v1; Thorin
    /// CGO 2015 flattens tuples into registers — the documented
    /// optimization path).
    TupleNew {
        dest: u16,
        args_start: u32,
        args_len: u16,
    },
    /// dest ← element `index` of the tuple in src.
    Extract { dest: u16, src: u16, index: u16 },
    /// dest ← rec with field `index` replaced by src (functional update —
    /// mutable value semantics; the Rc copy is CoW).
    SetField { dest: u16, rec: u16, src: u16, index: u16 },
    /// dest ← address of `count` fresh zero bytes (bump allocation).
    Alloc { dest: u16, count: u16 },
    /// dest ← one `kind`-sized read at the address in ptr.
    Load { dest: u16, ptr: u16, kind: MemKind },
    /// One `kind`-sized write of src at the address in ptr.
    Store { ptr: u16, src: u16, kind: MemKind },
    Copy { from: u16, to: u16, len: u16 },
    /// dest ← one io operation through the machine's IO boundary
    /// (POSIX return conventions; negative = errno). `a`, `b`, `c` are
    /// the operation's register operands in core/IO.tlk's IORequest
    /// order; unused trailing operands are 0. Pointer operands are
    /// marshaled against byte memory at execution (read fills it, open
    /// scans a NUL-terminated path, poll round-trips pollfd records).
    Io { dest: u16, op: IoOp, a: u16, b: u16, c: u16 },
    /// Call chunks[chunk] with args regs listed in the arg pool; the
    /// callee's Ret writes `dest` in this frame.
    Call {
        dest: u16,
        chunk: u32,
        args_start: u32,
        args_len: u16,
    },
    /// dest ← a flat closure over chunks[chunk]: captured values from the
    /// arg-pool registers, in the chunk's environment order (Cardelli,
    /// *Compiling a Functional Language*, LFP 1984).
    MakeClosure {
        dest: u16,
        chunk: u32,
        args_start: u32,
        args_len: u16,
    },
    /// dest ← the current frame's closure environment at `index`.
    EnvGet { dest: u16, index: u16 },
    /// Call the closure in register `callee` (its chunk, with its
    /// environment installed in the new frame).
    CallIndirect {
        dest: u16,
        callee: u16,
        args_start: u32,
        args_len: u16,
    },
    Jump { target: u32 },
    Branch { cond: u16, then_target: u32, else_target: u32 },
    /// Jump-table dispatch on an integer tag: targets live in the switch
    /// pool as [arm_0, …, arm_n, default]; a tag outside 0..n takes the
    /// default (decision-tree dispatch — Maranget, ML 2008).
    Switch {
        tag: u16,
        targets_start: u32,
        targets_len: u16,
    },
    Ret { src: u16 },
    /// A lowering/scheduling hole (unsupported construct); trapping keeps
    /// partial programs honest instead of silently misbehaving.
    Trap { message: u32 },
}

/// The io dialect — one operation per core/IO.tlk IORequest case.
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
}

#[derive(Debug)]
pub struct Chunk {
    pub name: String,
    pub code: Vec<Insn>,
    pub arity: u16,
    pub n_regs: u16,
}

#[derive(Debug, Default)]
pub struct Module {
    pub chunks: Vec<Chunk>,
    pub consts: Vec<interp::Value>,
    pub arg_pool: Vec<u16>,
    /// Jump-target lists for `Switch` instructions (default target last).
    pub switch_pool: Vec<u32>,
    pub traps: Vec<String>,
    /// Static memory image; the VM's byte memory starts as a copy (heap
    /// bump-allocates above it).
    pub statics: Vec<u8>,
    pub entry: u32,
}

impl Module {
    /// Human-readable listing (`talk ir`): one line per instruction, with
    /// pool references resolved — callee names instead of chunk indices,
    /// register lists instead of pool offsets, trap message text.
    pub fn render(&self) -> String {
        self.render_styled(&crate::lambda_g::print::Styles::plain())
    }

    pub fn render_ansi(&self) -> String {
        self.render_styled(&crate::lambda_g::print::Styles::ansi())
    }

    pub fn render_styled(&self, s: &crate::lambda_g::print::Styles) -> String {
        let mut out = String::new();
        for (i, chunk) in self.chunks.iter().enumerate() {
            out.push_str(&format!(
                "chunk {i}: {}{}{} (arity {}, regs {})\n",
                s.func, chunk.name, s.reset, chunk.arity, chunk.n_regs
            ));
            for (pc, insn) in chunk.code.iter().enumerate() {
                let text = self.render_insn(insn);
                // Color the mnemonic (the first word).
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
                format!("cmp_{} r{dest} <- r{a}, r{b}", format!("{op:?}").to_lowercase())
            }
            Insn::Trunc { dest, src } => format!("trunc r{dest} <- r{src}"),
            Insn::IToF { dest, src } => format!("itof r{dest} <- r{src}"),
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
            Insn::GetField { dest, rec, index } => {
                format!("get_field r{dest} <- r{rec}.{index}")
            }
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
            Insn::Load { dest, ptr, kind } => {
                format!("load_{} r{dest} <- [r{ptr}]", format!("{kind:?}").to_lowercase())
            }
            Insn::Store { ptr, src, kind } => {
                format!("store_{} [r{ptr}] <- r{src}", format!("{kind:?}").to_lowercase())
            }
            Insn::Copy { from, to, len } => format!("copy [r{to}] <- [r{from}], r{len} bytes"),
            Insn::Io { dest, op, a, b, c } => {
                format!(
                    "io_{} r{dest} <- r{a}, r{b}, r{c}",
                    format!("{op:?}").to_lowercase()
                )
            }
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
                format!(
                    "switch r{tag} -> [{}] default {default}",
                    arms.join(", ")
                )
            }
            Insn::Ret { src } => format!("ret r{src}"),
            Insn::Trap { message } => {
                format!("trap {:?}", self.traps[*message as usize])
            }
        }
    }
}
