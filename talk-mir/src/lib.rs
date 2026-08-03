//! Public finalized MIR: the one target seam (ADR 0047). The Talk
//! compiler publishes this data after ownership checking, optimization,
//! register allocation, and frame shaping; the bytecode, C, and LLVM
//! adapters consume exactly it.
//!
//! The module is trusted in-process data: construction invariants are
//! established by the compiler, and adapters report target errors for
//! malformed manually constructed values rather than replaying source
//! semantics.

pub mod layout;

pub use layout::{FieldRepr, Layout, LayoutId, ParamRepr, Shape, SlotKind};

pub type LocalId = u16;
pub type BlockId = usize;
pub type FuncId = usize;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Constant {
    Unit,
    Bool(bool),
    Int(i64),
    Float(f64),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Operand {
    Local(LocalId),
    Const(Constant),
}

/// Executable identity carried by finalized MIR instructions: the only
/// source-symbol facts that survive to targets (ADR 0047). `module` and
/// `local` mirror the source symbol's cross-module id. Display names are
/// metadata, never identity.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MirSymbol {
    pub kind: MirSymbolKind,
    pub module: u16,
    pub local: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MirSymbolKind {
    Struct,
    Enum,
    Effect,
    Protocol,
}

impl std::fmt::Debug for MirSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{:?}({}:{})", self.kind, self.module, self.local)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpKind {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// The E1 scalar operation vocabulary (`docs/backend-parity-ledger.md`).
#[derive(Clone, Copy, Debug)]
pub enum ScalarOp {
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    FloatAdd,
    FloatSub,
    FloatMul,
    FloatDiv,
    IntAnd,
    IntOr,
    IntXor,
    IntShl,
    IntShr,
    IntNot,
    ByteAnd,
    ByteOr,
    ByteXor,
    ByteShl,
    ByteShr,
    ByteNot,
    IntCmp(CmpKind),
    FloatCmp(CmpKind),
    ByteCmp(CmpKind),
    BoolCmp(CmpKind),
    FloatToIntTrunc,
    IntToFloat,
    ByteToInt,
    IntToByte,
}
#[derive(Clone, Debug)]
pub enum Inst {
    Copy {
        dest: LocalId,
        src: Operand,
    },
    Scalar {
        dest: LocalId,
        op: ScalarOp,
        a: Operand,
        b: Option<Operand>,
    },
    Call {
        dest: LocalId,
        func: FuncId,
        args: Vec<Operand>,
        /// Cleanup block entered if an effect abort unwinds through this
        /// call (ADR 0027); the block ends with `Term::UnwindRet`.
        unwind: Option<BlockId>,
    },
    /// Build an aggregate — struct, tuple, closed record, or enum
    /// value — flat under its layout (ADR 0045): identity lives in the
    /// layout table, and products are the `tag: 0` case of the one
    /// construction shape.
    Aggregate {
        dest: LocalId,
        tag: u16,
        layout: LayoutId,
        args: Vec<Operand>,
    },
    /// Read an enum value's tag as an Int.
    GetTag {
        dest: LocalId,
        src: Operand,
    },
    /// A struct cell awaiting an explicit initializer's field
    /// assignments: every field is Unit until the init body stores it.
    /// Only the uniform tagged representation can say "nothing here
    /// yet", so the destination never classes native — and because the
    /// blankness is declared rather than smuggled through unit-valued
    /// `Record` arguments, it does not break the layout's construction
    /// contract for honest sites (ADR 0045).
    Blank {
        dest: LocalId,
        layout: LayoutId,
    },
    /// Read one element of an aggregate — record field, tuple item, or
    /// variant payload (ADR 0045's collapsed read). A payload read
    /// carries the variant it reads from: the arm established the tag,
    /// and offset-addressed backends need it to place the element. The
    /// container's layout makes every read a static offset: MIR knows
    /// the container type at every emission site, so no backend infers
    /// a source's shape from dataflow.
    Field {
        dest: LocalId,
        src: Operand,
        /// The container's layout: native backends map the offset back
        /// to a struct member through it.
        container: LayoutId,
        /// The member's slot offset in the container (ADR 0046); a sum
        /// payload's offset already includes the tag slot.
        offset: u16,
        /// The spliced child's layout for an inline-aggregate member.
        member: Option<LayoutId>,
    },
    /// Read one member of a value whose container has no static shape —
    /// the existential boundary's writeback tuple (its payload element
    /// has no static width). Resolves through the value's own published
    /// layout at runtime.
    FieldIndex {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    /// Read an InlineArray element at a runtime-validated index. Carries
    /// the element's layout: the stride and per-element representation
    /// come from the published table, never from the value.
    GetElement {
        dest: LocalId,
        src: Operand,
        element: LayoutId,
        index: Operand,
    },
    /// Replace one stored field of a struct value in place.
    SetField {
        rec: LocalId,
        src: Operand,
        /// The container's layout; see `Field::container`.
        container: LayoutId,
        /// The member's slot offset in the container (ADR 0046).
        offset: u16,
        /// The spliced child's layout for an inline-aggregate member.
        member: Option<LayoutId>,
    },
    /// The write twin of `FieldIndex`: replace one member of a value
    /// whose container has no static shape.
    SetFieldIndex {
        rec: LocalId,
        src: Operand,
        index: u16,
    },
    /// A UTF-8 string literal; lowering interns the bytes as immortal
    /// static data and builds the core `String` value over them. Carries
    /// the published layouts of the String and its spliced Storage field
    /// so a backend builds the flat value without inferring them.
    StringLit {
        dest: LocalId,
        bytes: Vec<u8>,
        layout: LayoutId,
        storage_layout: LayoutId,
    },
    /// A raw pointer to interned immortal static bytes (string-literal
    /// pattern comparisons).
    BytesLit {
        dest: LocalId,
        bytes: Vec<u8>,
    },
    /// Allocate `bytes` bytes of managed memory.
    Alloc {
        dest: LocalId,
        bytes: Operand,
    },
    /// Release one reference to an allocation (frees at zero; statics are
    /// unmanaged no-ops).
    Free {
        src: Operand,
    },
    /// Add one reference to an allocation (statics are no-ops).
    RetainPtr {
        src: Operand,
    },
    IsUnique {
        dest: LocalId,
        src: Operand,
    },
    Load {
        dest: LocalId,
        ptr: Operand,
        kind: SlotKind,
    },
    Store {
        ptr: Operand,
        src: Operand,
        kind: SlotKind,
    },
    MemCopy {
        from: Operand,
        to: Operand,
        len: Operand,
    },
    /// `dest = ptr + offset * size`.
    PtrAdd {
        dest: LocalId,
        ptr: Operand,
        offset: Operand,
        size: u32,
    },
    /// A host IO operation: `op` indexes the runtime's operation table in
    /// core `IORequest` declaration order; unused operands pass zero.
    Io {
        dest: LocalId,
        op: u8,
        a: Operand,
        b: Operand,
        c: Operand,
    },
    /// Allocate a `'heap` object (its own fresh region, one claim).
    ObjectNew {
        dest: LocalId,
        args: Vec<Operand>,
    },
    ObjectGet {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    /// Store into an object field, merging the stored handles' regions
    /// into the object's (ADR 0033 merge-only regions).
    ObjectSet {
        obj: Operand,
        src: Operand,
        index: u16,
    },
    /// One live binding took / dropped a claim on every region reachable
    /// from the value's handles.
    RegionAcquire {
        src: Operand,
    },
    RegionRelease {
        src: Operand,
    },
    /// Build a function value: the chunk plus captured values (by value —
    /// handler-extent shared borrows in v1).
    MakeClosure {
        dest: LocalId,
        func: FuncId,
        env: Vec<Operand>,
    },
    /// Install a `'heap` object's finalizer: its `Deinit` hook runs as
    /// the region tears the object down (ADR 0033 lifecycle hooks).
    SetFinalizer {
        obj: Operand,
        closure: Operand,
    },
    /// Allocate a mutable cell (assignment conversion for captured
    /// mutable locals — Kranz et al., ORBIT, 1986). The handle is a
    /// copyable machine value; the closure and the defining frame share
    /// the cell through it.
    CellNew {
        dest: LocalId,
        init: Operand,
    },
    /// Read a cell's current value through its handle.
    CellGet {
        dest: LocalId,
        cell: Operand,
    },
    /// Overwrite a cell's value through its handle.
    CellSet {
        cell: Operand,
        src: Operand,
    },
    /// Call a function value.
    CallIndirect {
        dest: LocalId,
        callee: Operand,
        args: Vec<Operand>,
        unwind: Option<BlockId>,
    },
    /// Read one captured value from the executing closure's environment.
    EnvGet {
        dest: LocalId,
        index: u16,
    },
    /// Reify the current frame's return continuation (the delimiter of
    /// everything after a handler install in this frame).
    MakeCont {
        dest: LocalId,
    },
    /// Install a deep handler for the effect.
    PushHandler {
        effect: MirSymbol,
        clause: Operand,
        cont: Operand,
    },
    /// Nearest-handler routing for a perform site.
    FindHandler {
        clause: LocalId,
        cont: LocalId,
        index: LocalId,
        effect: MirSymbol,
    },
    GetFloor {
        dest: LocalId,
    },
    SetFloor {
        src: Operand,
    },
    /// Read a program global from its static slot (traps if read before
    /// its initializer ran — LINK-02).
    GlobalLoad {
        dest: LocalId,
        global: u32,
    },
    /// Write a program global's static slot.
    GlobalStore {
        global: u32,
        src: Operand,
    },
    /// Pack a concrete payload behind a protocol: `[drop, retain,
    /// requirement…]` witness closures at fixed slots (slot 0 drop,
    /// slot 1 retain, requirements from 2 — the archived convention).
    ExistentialPack {
        dest: LocalId,
        protocol: MirSymbol,
        payload: Operand,
        witnesses: Vec<Operand>,
    },
    ExistentialWitness {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    ExistentialPayload {
        dest: LocalId,
        src: Operand,
    },
    /// Discontinue: deliver `value` as the delimiter frame's return,
    /// unwinding every suspended frame through its cleanup (one-shot,
    /// Bruggeman, Waddell & Dybvig 1996; ADR 0027).
    AbortTo {
        cont: Operand,
        value: Operand,
    },
}

#[derive(Clone, Debug)]
pub enum Term {
    /// Jump to a block, passing one argument per block parameter
    /// (block-parameter SSA edges — Appel, *SSA is Functional
    /// Programming*, 1998; the builder keeps `Branch` argument-free by
    /// always routing merged values through dedicated arm blocks).
    Goto(BlockId, Vec<Operand>),
    Branch {
        cond: Operand,
        then_block: BlockId,
        else_block: BlockId,
    },
    /// Direct dispatch by a nonnegative enum tag. `targets[tag]` is the
    /// selected edge when present; every other value takes `default`.
    Switch {
        tag: Operand,
        targets: Vec<BlockId>,
        default: BlockId,
    },
    Return(Operand),
    Trap(&'static str),
    /// End of an unwind cleanup block.
    UnwindRet,
}

#[derive(Clone, Debug, Default)]
pub struct BlockData {
    /// Values this block receives from its predecessors' `Goto`
    /// arguments, defined at block entry.
    pub params: Vec<LocalId>,
    pub insts: Vec<Inst>,
    pub term: Option<Term>,
}

/// One frame local's published facts (ADR 0045): the locals table IS
/// the frame — its length is the local count — and each entry says what
/// the local holds and which substrate its reabstractions may use. The
/// facts are stamped by the compiler's frame shaping after register
/// allocation, on the numbering backends see; until then every entry is
/// the uniform default.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LocalInfo {
    /// The inline layout every definition of this local agrees on;
    /// `None` is a uniform tagged value.
    pub layout: Option<LayoutId>,
    /// Whether the value provably never leaves this frame (ADR 0044
    /// rule 3's substrate latch): reabstractions may then reuse frame
    /// storage instead of the arena.
    pub frame_local: bool,
}

impl LocalInfo {
    /// A frame of `count` uniform locals: the builder's shape before
    /// frame shaping stamps the facts.
    pub fn uniform(count: u16) -> Vec<LocalInfo> {
        vec![LocalInfo::default(); usize::from(count)]
    }
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub arity: u16,
    /// The frame: one entry per local (see [`LocalInfo`]).
    pub locals: Vec<LocalInfo>,
    pub blocks: Vec<BlockData>,
    /// Per-parameter value representation (ADR 0045): the layout each
    /// parameter arrives with, so a backend can give direct calls native
    /// signatures. Empty (synthesized bodies) means every parameter is a
    /// uniform tagged value.
    pub param_reprs: Vec<ParamRepr>,
    /// The return type's layout, when the body's types were in hand.
    pub return_repr: Option<LayoutId>,
    /// Construction sites, as `(block, instruction)`, whose value stays
    /// in this frame: the backend may give them reusable frame storage
    /// instead of the arena. Stamped by the compiler's frame shaping.
    pub frame_sites: std::collections::HashSet<(usize, usize)>,
}

impl Function {
    pub fn n_locals(&self) -> u16 {
        u16::try_from(self.locals.len()).unwrap_or(u16::MAX)
    }
}

/// How a displayed aggregate is rendered (its type-table kind).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeKind {
    Record,
    Enum,
    String,
}

/// One aggregate's display facts: its source name and its member names
/// (fields for records, variants for enums).
#[derive(Clone, Debug)]
pub struct DisplayEntry {
    pub name: String,
    pub kind: TypeKind,
    pub members: Vec<String>,
}

/// Type and member names for rendering a result the way the runtime
/// renders one. Names are metadata, never identity.
#[derive(Clone, Debug, Default)]
pub struct DisplayNames {
    pub entries: std::collections::HashMap<MirSymbol, DisplayEntry>,
}

/// The finalized module: every function of the program plus the facts
/// targets need to execute and render it (ADR 0047).
#[derive(Debug)]
pub struct Module {
    pub functions: Vec<Function>,
    pub entry: FuncId,
    /// Number of program globals (one 8-byte static slot each).
    pub global_slots: u32,
    /// Host-callable entry points (ADR 0043): export name → wrapper.
    pub exports: Vec<(String, FuncId)>,
    /// The interned layouts the aggregate instructions reference by
    /// `LayoutId` (ADR 0045): the shapes a backend must produce.
    pub layout_table: Vec<Layout>,
    /// Display metadata for the identities the layout table and
    /// existential packs carry.
    pub display: DisplayNames,
    /// The well-known runtime aggregate identities for String and
    /// Storage.
    pub string_symbol: MirSymbol,
    pub storage_symbol: MirSymbol,
}

impl Module {
    /// Render the middle representation for inspection (`talk mir`,
    /// TOOL-10). The shape is debug output, not a stable format.
    pub fn render(&self) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        let _ = writeln!(
            out,
            "entry: fn{} ({} global slots)",
            self.entry, self.global_slots
        );
        for (id, function) in self.functions.iter().enumerate() {
            let signature = if function.param_reprs.is_empty() && function.return_repr.is_none() {
                String::new()
            } else {
                format!(
                    ", params [{}] -> {}",
                    function
                        .param_reprs
                        .iter()
                        .map(|repr| repr.render())
                        .collect::<Vec<_>>()
                        .join(", "),
                    function
                        .return_repr
                        .map(|layout| format!("L{layout}"))
                        .unwrap_or_else(|| "uniform".into()),
                )
            };
            let _ = writeln!(
                out,
                "fn{id} {} (arity {}, locals {}{signature})",
                function.name, function.arity, function.n_locals()
            );
            for (block, data) in function.blocks.iter().enumerate() {
                let _ = writeln!(out, "  b{block}:");
                for inst in &data.insts {
                    // Aggregate constructions render their layout as a
                    // table id so shapes are legible next to the code.
                    match inst {
                        Inst::Aggregate {
                            dest,
                            tag,
                            layout,
                            args,
                        } => {
                            let _ = writeln!(
                                out,
                                "    Aggregate {{ dest: {dest}, tag: {tag}, layout: L{layout}, args: {args:?} }}"
                            );
                        }
                        Inst::Blank { dest, layout } => {
                            let _ = writeln!(
                                out,
                                "    Blank {{ dest: {dest}, layout: L{layout} }}"
                            );
                        }
                        _ => {
                            let _ = writeln!(out, "    {inst:?}");
                        }
                    }
                }
                if let Some(term) = &data.term {
                    let _ = writeln!(out, "    -> {term:?}");
                }
            }
        }
        if !self.layout_table.is_empty() {
            let _ = writeln!(out, "layout table:");
            for (id, layout) in self.layout_table.iter().enumerate() {
                let _ = writeln!(out, "  L{id}: {}", layout.render());
            }
        }
        out
    }
}
