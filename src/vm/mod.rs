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
    LoadByte { dest: u16, ptr: u16 },
    Copy { from: u16, to: u16, len: u16 },
    IoWrite { dest: u16, fd: u16, ptr: u16, len: u16 },
    /// Call chunks[chunk] with args regs listed in the arg pool; the
    /// callee's Ret writes `dest` in this frame.
    Call {
        dest: u16,
        chunk: u32,
        args_start: u32,
        args_len: u16,
    },
    Jump { target: u32 },
    Branch { cond: u16, then_target: u32, else_target: u32 },
    Ret { src: u16 },
    /// A lowering/scheduling hole (unsupported construct); trapping keeps
    /// partial programs honest instead of silently misbehaving.
    Trap { message: u32 },
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
    pub traps: Vec<String>,
    /// Static memory image; the VM's byte memory starts as a copy (heap
    /// bump-allocates above it).
    pub statics: Vec<u8>,
    pub entry: u32,
}
