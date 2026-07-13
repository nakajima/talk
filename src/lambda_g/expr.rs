//! λ_G types and expressions (Leißa & Griebler, Fig. 2 syntax, extended
//! with Talk's ground types and the `@_ir` primops in direct style — the
//! Thorin arrangement: control through continuations, primitive operations
//! as direct-style nodes; Leißa, Köster & Hack, CGO 2015).
//!
//! Expressions are immutable and hash-consed: structurally equal expressions
//! share one id (semi-global value numbering, paper §6.1 fn. 2; Sea of
//! Nodes: Click & Cooper, TOPLAS 1995). Local variables (LV) and local
//! functions (LF) are computed at construction (paper §3.1.1), so free
//! variables never re-traverse subexpressions.
//!
//! Types are fully annotated, so every expression's type is computed and
//! stored at construction (paper §3, "Typing"). Let-bindings are omitted:
//! sharing IS the let (paper §3: "explicit let-bindings unnecessary" in a
//! sea-of-nodes implementation).

use crate::lambda_g::program::Label;
use crate::lambda_g::sets::SetId;
use crate::name_resolution::symbol::Symbol;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TyId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TyKind {
    I64,
    F64,
    Bool,
    Byte,
    Ptr,
    Void,
    /// ⊥ — no inhabitants; functions into ⊥ are continuations (paper §2.2).
    Bot,
    Tuple(Box<[TyId]>),
    Fn(TyId, TyId),
    /// A Talk record/struct value (boxed at runtime; Leroy POPL 1992).
    Boxed(Symbol),
    /// A Talk enum value (tagged variant).
    Variant(Symbol),
    /// A first-class protocol existential: payload plus erased witness table.
    Existential(Symbol),
    /// A runtime-erased payload whose static type is a GADT-local skolem.
    Erased,
    /// A mutable cell (assignment-converted local — ORBIT-style).
    Cell(TyId),
    /// A `'heap` struct: values are region-allocated object handles with
    /// reference semantics (in-place mutation, aliasing).
    Object(Symbol),
}

impl TyKind {
    /// Bytes one value of this type occupies in raw memory: unboxed
    /// scalars in machine words (Leroy, *Unboxed objects and polymorphic
    /// typing*, POPL 1992 — Bool is one word too; byte-packing is a later,
    /// flagged optimization), aggregates as 8-byte handles into the boxed
    /// arena (see eval.rs / interp.rs). `None`: the type never lives in
    /// raw memory.
    pub fn mem_size(&self) -> Option<u32> {
        match self {
            TyKind::Byte => Some(1),
            TyKind::I64 | TyKind::F64 | TyKind::Bool | TyKind::Ptr => Some(8),
            TyKind::Boxed(_)
            | TyKind::Variant(_)
            | TyKind::Tuple(_)
            | TyKind::Existential(_)
            | TyKind::Erased => Some(8),
            // Objects never live in raw memory (region ledger can't scan it).
            TyKind::Void | TyKind::Bot | TyKind::Fn(..) | TyKind::Cell(_) | TyKind::Object(_) => {
                None
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Const {
    I64(i64),
    /// Bit pattern, so constants hash-cons.
    F64(u64),
    Bool(bool),
    Byte(u8),
    Void,
    /// An address in program memory (statics at the base, heap above —
    /// one space, so reified pointer values stay constants).
    StaticPtr(u32),
    /// A runtime cell handle, reified back into the term language by the
    /// evaluator (slots live in the machine, not the program).
    Slot(u32),
    /// A runtime object handle, reified back into the term language by the
    /// evaluator (objects live in the machine's region arena).
    Object(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Primitive operations: the `@_ir` dialect plus the lowerer-internal ops.
/// Control transfer (`Br`/`Switch`) is modeled as a primop rather than the
/// paper's built-in function `br_T` — same typing, simpler dispatch
/// (deviation noted; paper §2.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Cmp(CmpOp),
    Trunc,
    IToF,
    /// Byte → Int zero-extension.
    BToI,
    Alloc,
    Free,
    /// Add one reference to a heap buffer (a copy-on-write clone).
    Retain,
    /// Whether a heap buffer has exactly one reference.
    IsUnique,
    Load,
    Store,
    Copy,
    Swap(TyId),
    Move,
    Gep,
    RecordNew(Symbol),
    GetField(u32),
    SetField(u32),
    VariantNew(Symbol, u16),
    GetTag,
    GetPayload(u32),
    ExistentialPack(Symbol),
    ExistentialWitness(u32),
    ExistentialPayload,
    CellNew,
    CellGet,
    CellSet,
    /// Allocate a `'heap` object in a fresh region (args: initial fields).
    ObjectNew,
    /// Attach the finalizer thunk (args: [object, thunk-function-value]) —
    /// the thunk rides as a first-class function so closure conversion
    /// resolves its captures at the attachment site.
    SetFinalizer,
    /// In-place field read of a `'heap` object.
    ObjectGet(u32),
    /// In-place field store; storing a handle merges regions.
    ObjectSet(u32),
    /// Ledger: a binding took references into the value's regions.
    RegionAcquire,
    /// Ledger: a binding's references went out of scope; a region at zero
    /// tears down (finalizers in reverse allocation order, then bulk free).
    RegionRelease,
    /// Effect abort (ADR 0027): args [delimiter, value], ⊥-typed. Unwinds
    /// the suspended frames through their unwind entries, then delivers
    /// the value through the one-shot delimiter (the VM's `CallCont`).
    Abort,
    /// Terminates an unwind entry (⊥-typed, no args): the VM pops the
    /// unwound frame and continues the unwind; the evaluator's nested
    /// entry run completes.
    UnwindDone,
    /// Marks a `@handle` install for the evaluator's extent stack: args
    /// [delimiter]. The VM scheduler compiles it to nothing (the `Cont`'s
    /// frame index is the VM's marker).
    HandleInstall,
    /// args: [cond, then_thunk, else_thunk]; thunks have type [] → R.
    Br,
    /// args: [tag, k_0, …, k_n, default]; continuations [] → R.
    Switch,
    /// Total dispatch of an unhandled 'io perform on its IORequest variant
    /// (the implicit top-level handler — Plotkin & Pretnar, LMCS 2013).
    IoPerform,
    IoOpen,
    IoRead,
    IoWrite,
    IoClose,
    IoCtl,
    IoPoll,
    IoSocket,
    IoBind,
    IoListen,
    IoConnect,
    IoAccept,
    IoSleep,
    IoCwdLen,
    IoCwdCopy,
    IoGetenvLen,
    IoGetenvCopy,
    IoArgc,
    IoArgLen,
    IoArgCopy,
    IoDirCount,
    IoDirEntryKind,
    IoDirEntryLen,
    IoDirEntryCopy,
    IoExit,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExprKind {
    Const(Const),
    /// ℓ — a reference to the function itself.
    Func(Label),
    /// var ℓ — the function's variable (its argument).
    Var(Label),
    /// Application. The third operand is the optional **unwind entry**
    /// (ADR 0027): a `Fn(Void, ⊥)` continuation holding this suspension
    /// site's scope-exit drops, entered once if an effect abort unwinds
    /// through the frame suspended at this call. Structural (not a side
    /// map) so fv/subst/check/print/schedule all see it.
    App(ExprId, ExprId, Option<ExprId>),
    Tuple(Box<[ExprId]>),
    Extract(ExprId, u32),
    PrimOp(Op, Box<[ExprId]>, TyId),
}

/// An interned expression: kind, type (T-rules at construction), and the
/// LV/LF sets stored at construction (paper §3.1, Eqs. 1–6).
#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: TyId,
    pub lv: SetId,
    pub lf: SetId,
}
