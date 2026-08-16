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

impl MirSymbol {
    /// The well-known runtime aggregate identities (ADR 0047): String,
    /// its Storage field, and the InlineArray construction identity. The
    /// compiler's own mapping is pinned against these constants by its
    /// tests, so the two cannot drift.
    pub const STRING: MirSymbol = MirSymbol {
        kind: MirSymbolKind::Struct,
        module: 1,
        local: u32::MAX - 32,
    };

    pub const STORAGE: MirSymbol = MirSymbol {
        kind: MirSymbolKind::Struct,
        module: 1,
        local: u32::MAX - 30,
    };

    pub const INLINE_ARRAY: MirSymbol = MirSymbol {
        kind: MirSymbolKind::Struct,
        module: 1,
        local: u32::MAX - 22,
    };
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
    PtrCmp(CmpKind),
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
    /// ADR 0058 task runtime: start a worker running the `worker`
    /// closure (a `() -> T` function value, consumed) and produce an
    /// executor-internal handle. Whether the worker runs on another OS
    /// thread or inline is runtime policy, never semantics.
    TaskSpawn {
        dest: LocalId,
        arg: Operand,
        worker: Operand,
    },
    /// ADR 0058 task runtime: join the worker behind `handle`,
    /// transferring its output to `dest`. Joining an invalid or
    /// already-joined handle is a trap.
    TaskJoin {
        dest: LocalId,
        handle: Operand,
    },
    /// ADR 0058 task runtime: the host's available parallelism (>= 1).
    TaskWidth {
        dest: LocalId,
    },
    /// ADR 0059: enqueue a transferred value on the channel behind
    /// `handle` and wake its waiter. The value moves; `Send` was checked
    /// upstream.
    ChanSend {
        handle: Operand,
        value: Operand,
    },
    /// ADR 0059: take a queued value off the channel behind `handle`
    /// (trap when none — callers gate on status first).
    ChanTake {
        dest: LocalId,
        handle: Operand,
    },
    /// ADR 0059: scalar channel/park control (create, status, side
    /// retain/drop, external-wait register/unregister, park).
    ChanCtl {
        dest: LocalId,
        handle: Operand,
        op: Operand,
    },
    /// ADR 0064/0068: perform against a resumption-binding handler —
    /// capture the extent from the installing frame through this site
    /// into a stored one-shot resumption and run the clause in the
    /// installer's place. `dest` receives the value a later `Resume`
    /// supplies. Emitted under a clause-kind branch on the entry a
    /// `FindHandler` located; `entry` is that handler's stack index.
    Suspend {
        dest: LocalId,
        effect: MirSymbol,
        args: Vec<Operand>,
        entry: Operand,
        /// Cleanup block for an abort or cancellation unwinding through
        /// the suspended frame (ADR 0027's per-call machinery; the
        /// release planner backfills it like a call's).
        unwind: Option<BlockId>,
    },
    /// ADR 0064: resume a stored resumption with a value; `dest`
    /// receives the extent's answer when it finishes or aborts.
    Resume {
        dest: LocalId,
        cont: Operand,
        value: Operand,
    },
    /// ADR 0064: cancel a stored resumption, unwinding its captured
    /// frames through their cleanup entries (ADR 0027's machinery).
    Cancel { cont: Operand },
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
    /// Install a deep handler for the effect. `binds` records the
    /// clause's kind (ADR 0068): true when it binds the stored
    /// resumption as a final parameter, false when it is
    /// tail-resumptive and runs as a call at the perform site.
    PushHandler {
        effect: MirSymbol,
        clause: Operand,
        cont: Operand,
        binds: bool,
    },
    /// Nearest-handler routing for a perform site. `binds` receives the
    /// matched entry's clause kind (ADR 0068), the runtime branch
    /// between the suspend and call protocols.
    FindHandler {
        clause: LocalId,
        cont: LocalId,
        index: LocalId,
        binds: LocalId,
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

/// Source provenance for one instruction, resolved when the compiler
/// collects it: `file` indexes [`Module::debug_files`], `line`/`col`
/// are 1-based, and `start`/`end` are the statement's byte offsets for
/// consumers that want to link back to the source text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DebugSpan {
    pub file: u32,
    pub line: u32,
    pub col: u32,
    pub start: u32,
    pub end: u32,
}

/// Why an instruction exists in finalized MIR.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DebugOrigin {
    Source(DebugSpan),
    Generated(GeneratedMir),
}

/// Where ownership cleanup runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CleanupKind {
    Unwind,
    BlockExit,
    Edge,
}

impl CleanupKind {
    fn description(self) -> &'static str {
        match self {
            Self::Unwind => "effect-unwind cleanup",
            Self::BlockExit => "block-exit cleanup",
            Self::Edge => "control-flow-edge cleanup",
        }
    }
}

/// Compiler-owned reasons for emitting MIR without a direct source span.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeneratedMir {
    FrontendDesugaring,
    ClosureCapture {
        local: LocalId,
        env_index: u16,
        closure_at: Option<DebugSpan>,
    },
    ClosureWitness {
        local: LocalId,
        env_index: u16,
        closure_at: Option<DebugSpan>,
    },
    HandlerDelimiter {
        local: LocalId,
        env_index: u16,
        handler_at: Option<DebugSpan>,
    },
    FunctionEpilogue,
    Cleanup {
        kind: CleanupKind,
        local: LocalId,
        created_at: Option<DebugSpan>,
    },
    ProgramEntry,
    GlobalInitialization,
    ExportAdapter,
    HeapTeardown,
    DropGlue,
    RetainGlue,
    DerivedShow,
    DerivedEquality,
    DerivedIdentity,
    RequirementForwarder,
    EnumConstructor,
}

impl GeneratedMir {
    fn description(self) -> &'static str {
        match self {
            Self::FrontendDesugaring => "frontend desugaring",
            Self::ClosureCapture { .. } => "closure capture binding",
            Self::ClosureWitness { .. } => "closure witness binding",
            Self::HandlerDelimiter { .. } => "effect-handler delimiter binding",
            Self::FunctionEpilogue => "implicit function return and writeback",
            Self::Cleanup { .. } => "ownership cleanup",
            Self::ProgramEntry => "program entry and global teardown wrapper",
            Self::GlobalInitialization => "top-level global initialization",
            Self::ExportAdapter => "host-callable export adapter",
            Self::HeapTeardown => "heap object teardown",
            Self::DropGlue => "type-specific value destruction",
            Self::RetainGlue => "type-specific value retain",
            Self::DerivedShow => "derived Showable implementation",
            Self::DerivedEquality => "derived Equatable implementation",
            Self::DerivedIdentity => "derived reflexive Into implementation",
            Self::RequirementForwarder => "protocol requirement witness forwarding",
            Self::EnumConstructor => "first-class enum constructor",
        }
    }
}

/// Per-instruction provenance for one block, aligned with
/// [`BlockData::insts`].
#[derive(Clone, Debug)]
pub struct BlockDebug {
    pub origins: Vec<DebugOrigin>,
}

#[derive(Clone, Debug, Default)]
pub struct BlockData {
    /// Values this block receives from its predecessors' `Goto`
    /// arguments, defined at block entry.
    pub params: Vec<LocalId>,
    pub insts: Vec<Inst>,
    pub term: Option<Term>,
    /// Source provenance per instruction (debug-mode compiles only);
    /// `None` in production modules.
    pub debug: Option<Box<BlockDebug>>,
}

impl BlockData {
    /// A block that records instruction provenance when `debug` is on.
    pub fn debugged(debug: bool) -> Self {
        Self {
            debug: debug.then_some(Box::new(BlockDebug {
                origins: Vec::new(),
            })),
            ..Self::default()
        }
    }

    /// Push an instruction, recording its provenance when this block
    /// carries debug metadata.
    pub fn push_inst(&mut self, inst: Inst, origin: DebugOrigin) {
        if let Some(debug) = &mut self.debug {
            debug.origins.push(origin);
        }
        self.insts.push(inst);
    }

    /// Retain matching instructions, keeping debug origins aligned.
    pub fn retain_insts(&mut self, mut keep: impl FnMut(&Inst) -> bool) {
        let Some(debug) = &mut self.debug else {
            self.insts.retain(keep);
            return;
        };
        debug_assert_eq!(debug.origins.len(), self.insts.len());
        let origins = std::mem::take(&mut debug.origins);
        let mut next = origins.iter();
        let mut kept = Vec::with_capacity(origins.len());
        self.insts.retain(|inst| {
            let origin = next
                .next()
                .copied()
                .expect("aligned debug origin exists for every instruction");
            let keep = keep(inst);
            if keep {
                kept.push(origin);
            }
            keep
        });
        debug.origins = kept;
    }

    /// Drain a range of instructions, keeping debug origins aligned.
    pub fn drain_insts(&mut self, range: std::ops::Range<usize>) {
        if let Some(debug) = &mut self.debug {
            debug.origins.drain(range.clone());
        }
        self.insts.drain(range);
    }

    /// Remove the instruction at `index`, keeping debug origins aligned.
    pub fn remove_inst(&mut self, index: usize) -> Inst {
        if let Some(debug) = &mut self.debug {
            debug.origins.remove(index);
        }
        self.insts.remove(index)
    }

    /// Whether every instruction has a matching debug-origin slot.
    pub fn debug_is_aligned(&self) -> bool {
        self.debug
            .as_ref()
            .is_none_or(|debug| debug.origins.len() == self.insts.len())
    }
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
    /// Binding names per local (debug-mode compiles only), indexed by
    /// `LocalId`; empty strings are unnamed, and a register reused for
    /// several bindings lists them all. `None` in production modules.
    pub debug_names: Option<Vec<String>>,
}

impl Function {
    pub fn n_locals(&self) -> u16 {
        u16::try_from(self.locals.len()).unwrap_or(u16::MAX)
    }

    fn debug_local(&self, local: LocalId) -> String {
        match self
            .debug_names
            .as_ref()
            .and_then(|names| names.get(usize::from(local)))
            .filter(|name| !name.is_empty())
        {
            Some(name) => format!("L{local}({name})"),
            None => format!("L{local}"),
        }
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
    /// The file paths [`DebugSpan::file`] indexes; empty unless the
    /// module was compiled in debug mode.
    pub debug_files: Vec<String>,
    /// Source text aligned with `debug_files`, used to show the exact
    /// source construct for each contiguous MIR origin group.
    pub debug_sources: Vec<String>,
}

impl Module {
    fn debug_snippet(&self, span: DebugSpan) -> Option<String> {
        let source = self.debug_sources.get(span.file as usize)?;
        let start = usize::try_from(span.start).ok()?;
        let end = usize::try_from(span.end).ok()?;
        let mut snippet = source
            .get(start..end)?
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        const MAX_SNIPPET_CHARS: usize = 120;
        if snippet.chars().count() > MAX_SNIPPET_CHARS {
            snippet = snippet.chars().take(MAX_SNIPPET_CHARS - 3).collect();
            snippet.push_str("...");
        }
        (!snippet.is_empty()).then_some(snippet)
    }

    fn debug_location(&self, span: DebugSpan) -> String {
        let file = self
            .debug_files
            .get(span.file as usize)
            .map(String::as_str)
            .unwrap_or("?");
        match self.debug_snippet(span) {
            Some(snippet) => format!("{file}:{}:{}: {snippet}", span.line, span.col),
            None => format!("{file}:{}:{}", span.line, span.col),
        }
    }

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
                function.name,
                function.arity,
                function.n_locals()
            );
            if let Some(names) = &function.debug_names {
                let named: Vec<String> = names
                    .iter()
                    .enumerate()
                    .filter(|(_, name)| !name.is_empty())
                    .map(|(local, name)| format!("L{local}({name})"))
                    .collect();
                if !named.is_empty() {
                    let _ = writeln!(out, "  // locals: {}", named.join(", "));
                }
            }
            for (block, data) in function.blocks.iter().enumerate() {
                let _ = writeln!(out, "  b{block}:");
                let debug = !self.debug_sources.is_empty();
                let mut last_origin: Option<DebugOrigin> = None;
                for (index, inst) in data.insts.iter().enumerate() {
                    let origin = data
                        .debug
                        .as_ref()
                        .and_then(|debug| debug.origins.get(index).copied());
                    if debug && (index == 0 || origin != last_origin) {
                        if index != 0 {
                            let _ = writeln!(out);
                        }
                        match origin {
                            Some(DebugOrigin::Source(span)) => {
                                let file = self
                                    .debug_files
                                    .get(span.file as usize)
                                    .map(String::as_str)
                                    .unwrap_or("?");
                                if let Some(snippet) = self.debug_snippet(span) {
                                    let _ = writeln!(
                                        out,
                                        "    // source {file}:{}:{}: {snippet}",
                                        span.line, span.col
                                    );
                                } else {
                                    let _ = writeln!(
                                        out,
                                        "    // source {file}:{}:{}",
                                        span.line, span.col
                                    );
                                }
                            }
                            Some(DebugOrigin::Generated(GeneratedMir::Cleanup {
                                kind,
                                local,
                                created_at,
                            })) => {
                                let target = function.debug_local(local);
                                if let Some(span) = created_at {
                                    let file = self
                                        .debug_files
                                        .get(span.file as usize)
                                        .map(String::as_str)
                                        .unwrap_or("?");
                                    if let Some(snippet) = self.debug_snippet(span) {
                                        let _ = writeln!(
                                            out,
                                            "    // generated MIR: {} of {target}, created by {file}:{}:{}: {snippet}",
                                            kind.description(),
                                            span.line,
                                            span.col
                                        );
                                    } else {
                                        let _ = writeln!(
                                            out,
                                            "    // generated MIR: {} of {target}, created by {file}:{}:{}",
                                            kind.description(),
                                            span.line,
                                            span.col
                                        );
                                    }
                                } else {
                                    let _ = writeln!(
                                        out,
                                        "    // generated MIR: {} of {target}",
                                        kind.description()
                                    );
                                }
                            }
                            Some(DebugOrigin::Generated(GeneratedMir::ClosureCapture {
                                local,
                                env_index,
                                closure_at,
                            })) => {
                                let local = function.debug_local(local);
                                let location = closure_at
                                    .map(|span| format!(" at {}", self.debug_location(span)))
                                    .unwrap_or_default();
                                let _ = writeln!(
                                    out,
                                    "    // generated MIR: bind capture {local} from env[{env_index}] for closure fn{id} {}{location}",
                                    function.name
                                );
                            }
                            Some(DebugOrigin::Generated(GeneratedMir::ClosureWitness {
                                local,
                                env_index,
                                closure_at,
                            })) => {
                                let local = function.debug_local(local);
                                let location = closure_at
                                    .map(|span| format!(" at {}", self.debug_location(span)))
                                    .unwrap_or_default();
                                let _ = writeln!(
                                    out,
                                    "    // generated MIR: bind witness {local} from env[{env_index}] for closure fn{id} {}{location}",
                                    function.name
                                );
                            }
                            Some(DebugOrigin::Generated(GeneratedMir::HandlerDelimiter {
                                local,
                                env_index,
                                handler_at,
                            })) => {
                                let local = function.debug_local(local);
                                let location = handler_at
                                    .map(|span| format!(" at {}", self.debug_location(span)))
                                    .unwrap_or_default();
                                let _ = writeln!(
                                    out,
                                    "    // generated MIR: bind handler delimiter {local} from env[{env_index}] for fn{id} {}{location}",
                                    function.name
                                );
                            }
                            Some(DebugOrigin::Generated(reason)) => {
                                let _ =
                                    writeln!(out, "    // generated MIR: {}", reason.description());
                            }
                            None => {
                                let _ = writeln!(out, "    // MIR origin unavailable");
                            }
                        }
                    }
                    last_origin = origin;
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
                            let _ =
                                writeln!(out, "    Blank {{ dest: {dest}, layout: L{layout} }}");
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_prints_debug_comments_and_local_names() {
        let span = DebugSpan {
            file: 0,
            line: 4,
            col: 3,
            start: 0,
            end: 9,
        };
        let module = Module {
            debug_files: vec!["playground.tlk".into()],
            debug_sources: vec!["value = 1".into()],
            functions: vec![Function {
                debug_names: Some(vec!["value".into(), String::new()]),
                frame_sites: Default::default(),
                param_reprs: Vec::new(),
                return_repr: None,
                name: "main".into(),
                arity: 0,
                locals: LocalInfo::uniform(2),
                blocks: vec![BlockData {
                    debug: Some(Box::new(BlockDebug {
                        origins: vec![
                            DebugOrigin::Source(span),
                            DebugOrigin::Source(span),
                            DebugOrigin::Generated(GeneratedMir::Cleanup {
                                kind: CleanupKind::BlockExit,
                                local: 1,
                                created_at: None,
                            }),
                            DebugOrigin::Source(span),
                        ],
                    })),
                    params: Vec::new(),
                    insts: vec![
                        Inst::Copy {
                            dest: 0,
                            src: Operand::Const(Constant::Int(1)),
                        },
                        Inst::Copy {
                            dest: 1,
                            src: Operand::Local(0),
                        },
                        Inst::Free {
                            src: Operand::Local(1),
                        },
                        Inst::Copy {
                            dest: 0,
                            src: Operand::Const(Constant::Int(2)),
                        },
                    ],
                    term: Some(Term::Return(Operand::Local(0))),
                }],
            }],
            entry: 0,
            global_slots: 0,
            exports: Vec::new(),
            layout_table: Vec::new(),
            display: DisplayNames::default(),
            string_symbol: MirSymbol::STRING,
            storage_symbol: MirSymbol::STORAGE,
        };

        let rendered = module.render();
        assert!(rendered.contains("// locals: L0(value)"));
        assert_eq!(
            rendered
                .matches("// source playground.tlk:4:3: value = 1")
                .count(),
            2
        );
        assert!(rendered.contains("// generated MIR: block-exit cleanup of L1"));
    }
}
