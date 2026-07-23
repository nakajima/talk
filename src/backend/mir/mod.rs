//! Source-level middle representation and its builder.
//!
//! MIR is the backend's one control-flow graph over the frontend's typed
//! tree (ADR 0034). Functions become basic blocks of scalar instructions;
//! pattern matches compile to branch chains (a degenerate decision tree in
//! the sense of Maranget 2008, "Compiling Pattern Matching to Good Decision
//! Trees" — wave 2 grows the real tree). Everything in wave 1 is a Copy
//! scalar, so ownership checking is the type gate in `scalar_ty`.

use rustc_hash::FxHashMap;

use crate::compiling::typed_program::TypedProgram;
use crate::name::Name;
mod entries;
mod glue;
mod release;
mod unsafe_gate;
mod verify;

/// The rigid-generic witnesses a closure environment carries: for each
/// inherited type parameter, its `(drop, retain)` witness locals.
type WitnessPairs = Vec<(Symbol, (LocalId, LocalId))>;

use crate::name_resolution::symbol::Symbol;
use crate::node_kinds::call_arg::ArgMode;
use crate::node_kinds::inline_ir_instruction::{InlineIRInstructionKind, Value as IrValue};
use crate::parsing::span::Span;
use crate::token_kind::TokenKind;
use crate::typed_ast::{
    Block, Decl, DeclKind, Expr, ExprKind, Func, Literal, Node, Pattern, PatternKind,
    RecordFieldPattern, RecordFieldPatternKind, Stmt, StmtKind,
};
use crate::types::output::CheckedIntegerLiteral;
use crate::types::ty::{ParamKind, Perm, ProtocolRef, StaticValue, Ty};

use super::BackendError;

pub(crate) type LocalId = u16;
pub(crate) type BlockId = usize;
pub(crate) type FuncId = usize;

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Constant {
    Unit,
    Bool(bool),
    Int(i64),
    Float(f64),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Operand {
    Local(LocalId),
    Const(Constant),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CmpKind {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// The E1 scalar operation vocabulary (`docs/e1-scalar-execution-plan.md`).
#[derive(Clone, Copy, Debug)]
pub(crate) enum ScalarOp {
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
}

#[derive(Clone, Debug)]
pub(crate) enum Inst {
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
    /// Build a tuple from element operands.
    Tuple {
        dest: LocalId,
        args: Vec<Operand>,
    },
    /// Read one positional element of a tuple.
    TupleGet {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    /// Build an enum value with its declaration-order tag.
    Variant {
        dest: LocalId,
        enum_symbol: Symbol,
        tag: u16,
        args: Vec<Operand>,
    },
    /// Read an enum value's tag as an Int.
    GetTag {
        dest: LocalId,
        src: Operand,
    },
    /// Read one payload element of an enum value.
    GetPayload {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    /// Build a struct value with fields in declaration order.
    Record {
        dest: LocalId,
        struct_symbol: Symbol,
        args: Vec<Operand>,
    },
    /// Read one stored field of a struct value.
    GetField {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    /// Read an InlineArray element at a runtime-validated index.
    GetElement {
        dest: LocalId,
        src: Operand,
        index: Operand,
    },
    /// Replace one stored field of a struct value in place.
    SetField {
        rec: LocalId,
        src: Operand,
        index: u16,
    },
    /// A UTF-8 string literal; lowering interns the bytes as immortal
    /// static data and builds the core `String` value over them.
    StringLit {
        dest: LocalId,
        bytes: Vec<u8>,
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
        kind: MemTy,
    },
    Store {
        ptr: Operand,
        src: Operand,
        kind: MemTy,
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
        effect: Symbol,
        clause: Operand,
        cont: Operand,
    },
    /// Nearest-handler routing for a perform site.
    FindHandler {
        clause: LocalId,
        cont: LocalId,
        index: LocalId,
        effect: Symbol,
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
        protocol: Symbol,
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

/// The sized memory element classes the target knows (byte loads are one
/// byte; every other class is one 8-byte word).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MemTy {
    Byte,
    I64,
    F64,
    Bool,
    Ptr,
    Boxed,
}

impl MemTy {
    pub(crate) fn size(self) -> u32 {
        match self {
            MemTy::Byte => 1,
            _ => 8,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum Term {
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
    Return(Operand),
    Trap(&'static str),
    /// End of an unwind cleanup block.
    UnwindRet,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BlockData {
    /// Values this block receives from its predecessors' `Goto`
    /// arguments, defined at block entry.
    pub params: Vec<LocalId>,
    pub insts: Vec<Inst>,
    pub term: Option<Term>,
}

#[derive(Debug)]
pub(crate) struct Function {
    pub name: String,
    pub arity: u16,
    pub n_locals: u16,
    pub blocks: Vec<BlockData>,
}

#[derive(Debug)]
pub(crate) struct Program {
    pub functions: Vec<Function>,
    pub entry: FuncId,
    /// Number of program globals (one 8-byte static slot each).
    pub global_slots: u32,
}

impl Program {
    /// Render the middle representation for inspection (`talk mir`,
    /// TOOL-10). The shape is debug output, not a stable format.
    pub(crate) fn render(&self) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        let _ = writeln!(
            out,
            "entry: fn{} ({} global slots)",
            self.entry, self.global_slots
        );
        for (id, function) in self.functions.iter().enumerate() {
            let _ = writeln!(
                out,
                "fn{id} {} (arity {}, locals {})",
                function.name, function.arity, function.n_locals
            );
            for (block, data) in function.blocks.iter().enumerate() {
                let _ = writeln!(out, "  b{block}:");
                for inst in &data.insts {
                    let _ = writeln!(out, "    {inst:?}");
                }
                if let Some(term) = &data.term {
                    let _ = writeln!(out, "    -> {term:?}");
                }
            }
        }
        out
    }
}

/// How execution starts (`talk run`): a script's top-level statements, or a
/// named zero-parameter public function.
pub(crate) enum Entry<'a> {
    Script,
    Named(&'a str),
}

/// The scalar value classification wave 1 accepts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ScalarTy {
    Unit,
    Bool,
    Int,
    Float,
    Byte,
    Ptr,
    Never,
}

fn scalar_ty(ty: &Ty, span: Span) -> Result<ScalarTy, BackendError> {
    // Shared loans of Copy scalars erase at execution (ledger BOR-01): a
    // borrowed Int is an Int in the target.
    if let Ty::Borrow(_, inner) = ty {
        return scalar_ty(inner, span);
    }
    if let Ty::Nominal(symbol, args) = ty
        && args.is_empty()
    {
        let scalar = [
            (Symbol::Void, ScalarTy::Unit),
            (Symbol::Bool, ScalarTy::Bool),
            (Symbol::Int, ScalarTy::Int),
            (Symbol::Float, ScalarTy::Float),
            (Symbol::Byte, ScalarTy::Byte),
            (Symbol::RawPtr, ScalarTy::Ptr),
            (Symbol::Never, ScalarTy::Never),
        ]
        .into_iter()
        .find(|(known, _)| known == symbol);
        if let Some((_, scalar)) = scalar {
            return Ok(scalar);
        }
    }
    Err(BackendError::unsupported(
        format!(
            "values of type `{}` are not supported yet",
            ty.render_mono()
        ),
        span,
    ))
}

/// A callable found in one of the compiled programs' typed trees. Instance
/// methods already carry their receiver as an explicit first parameter
/// (`self` is params[0] in the typed tree); explicit initializers get their
/// fresh `self` record from the caller the same way.
#[derive(Clone, Copy)]
struct Callable<'a> {
    body: CallableBody<'a>,
    /// Which program the body came from (for its `TypeOutput` side tables).
    program: usize,
    /// The declared receiver mode for methods (`mut func` receivers write
    /// back through the private tuple-return convention).
    receiver: crate::node_kinds::decl::ReceiverMode,
}

#[derive(Clone, Copy)]
enum CallableBody<'a> {
    Func(&'a Func),
    Init {
        params: &'a [crate::typed_ast::Parameter],
        body: &'a Block,
    },
}

impl<'a> CallableBody<'a> {
    fn name(&self) -> String {
        match self {
            CallableBody::Func(func) => func.name.name_str(),
            CallableBody::Init { .. } => "init".into(),
        }
    }

    fn scheme_params(&self) -> &'a [crate::types::ty::SchemeParam] {
        match self {
            CallableBody::Func(func) => &func.scheme.params,
            CallableBody::Init { .. } => &[],
        }
    }

    fn scheme_ty(&self) -> Option<&'a Ty> {
        match self {
            CallableBody::Func(func) => Some(&func.scheme.ty),
            CallableBody::Init { .. } => None,
        }
    }
}

/// One typed program in the reachable compilation graph, with the module
/// identity importers see its symbols under.
pub(crate) struct ProgramInput<'a> {
    pub program: &'a TypedProgram,
    pub module: crate::compiling::module::ModuleId,
}

/// A program's files ordered so a file's local imports initialize
/// before it (LINK-02: deterministic, dependency-first globals).
/// Import edges come from `use package::Module` markers matched to
/// sibling file stems; files without edges keep their discovery order,
/// and a cycle falls back to discovery order for the remainder.
fn files_in_initialization_order(program: &TypedProgram) -> Vec<&crate::typed_ast::TypedFile> {
    use crate::node_kinds::decl::ImportPath;
    let files: Vec<(
        &crate::compiling::driver::Source,
        &crate::typed_ast::TypedFile,
    )> = program.files().iter().collect();
    let position: FxHashMap<String, usize> = files
        .iter()
        .enumerate()
        .filter_map(|(index, (source, _))| {
            source
                .source_path()
                .and_then(|path| path.file_stem())
                .and_then(|stem| stem.to_str())
                .map(|stem| (stem.to_string(), index))
        })
        .collect();
    let mut deps: Vec<Vec<usize>> = vec![Vec::new(); files.len()];
    for (index, (_, file)) in files.iter().enumerate() {
        for root in &file.roots {
            if let Node::Decl(decl) = root
                && let DeclKind::Import(import) = &decl.kind
                && let ImportPath::Local(path) = &import.path
                && let Some(stem) = path.rsplit("::").next()
                && let Some(&target) = position.get(stem)
                && target != index
            {
                deps[index].push(target);
            }
        }
    }
    // Depth-first with insertion-order roots: every file keeps its
    // discovery position except that its imports hoist ahead of it; a
    // cycle breaks at the back edge.
    fn visit(index: usize, deps: &[Vec<usize>], state: &mut [u8], order: &mut Vec<usize>) {
        if state[index] != 0 {
            return;
        }
        state[index] = 1;
        for &dep in &deps[index] {
            if state[dep] == 0 {
                visit(dep, deps, state, order);
            }
        }
        state[index] = 2;
        order.push(index);
    }
    let mut state = vec![0u8; files.len()];
    let mut indexes = Vec::with_capacity(files.len());
    for index in 0..files.len() {
        visit(index, &deps, &mut state, &mut indexes);
    }
    indexes.into_iter().map(|index| files[index].1).collect()
}

/// A top-level `func name(...)` declaration desugars to `let name = <func>`;
/// the binding is the callable's identity for calls and entry selection.
fn let_bound_func(decl: &Decl) -> Option<(&Name, &Func)> {
    let DeclKind::Let {
        lhs,
        rhs: Some(rhs),
        ..
    } = &decl.kind
    else {
        return None;
    };
    let PatternKind::Bind(name) = &lhs.kind else {
        return None;
    };
    let ExprKind::Func(func) = &rhs.kind else {
        return None;
    };
    Some((name, func))
}

/// Whether values of this type own refcounted buffers anywhere (RawPtr
/// leaves). The visited set breaks recursive nominals.
fn contains_buffer(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {
    if let Some(&known) = builder.contains_buffer_cache.borrow().get(ty) {
        return known;
    }
    let computed = contains_guarded(builder, ty, &BUFFER_WALK, &mut Vec::new());
    builder
        .contains_buffer_cache
        .borrow_mut()
        .insert(ty.clone(), computed);
    computed
}

/// One recursive containment walk serves both ownership questions
/// (buffers, `'heap` objects): strip borrows, test the nominal leaf,
/// recurse through fields, payloads, tuples, and records, with a
/// visited guard for recursive nominals.
struct ContainsWalk {
    /// Decides a nominal leaf before recursion: RawPtr owns a buffer,
    /// a `'heap` struct is an object. `None` recurses structurally.
    leaf: fn(&ProgramBuilder<'_>, Symbol) -> Option<bool>,
    /// Whether a rigid effect-generic counts (buffers: yes, so retains
    /// and drops route through its witnesses).
    param_counts: bool,
    /// Whether borrowed enum payloads are skipped (a view owns nothing).
    skip_borrowed_payloads: bool,
}

fn contains_guarded(
    builder: &ProgramBuilder<'_>,
    ty: &Ty,
    walk: &ContainsWalk,
    visiting: &mut Vec<Symbol>,
) -> bool {
    let mut ty = ty;
    while let Ty::Borrow(_, inner) = ty {
        ty = inner;
    }
    match ty {
        Ty::Nominal(symbol, args) => {
            if let Some(decided) = (walk.leaf)(builder, *symbol) {
                return decided;
            }
            if visiting.contains(symbol) {
                return false;
            }
            visiting.push(*symbol);
            let result = if let Some(fields) = builder.field_types(*symbol, args) {
                fields
                    .iter()
                    .any(|field| contains_guarded(builder, field, walk, visiting))
            } else if let Some(payloads) = builder.variant_payloads(*symbol, args) {
                payloads.iter().flatten().any(|payload| {
                    !(walk.skip_borrowed_payloads && matches!(payload, Ty::Borrow(_, _)))
                        && contains_guarded(builder, payload, walk, visiting)
                })
            } else {
                false
            };
            visiting.pop();
            result
        }
        Ty::Tuple(items) => items
            .iter()
            .any(|item| contains_guarded(builder, item, walk, visiting)),
        Ty::Record(row) => row
            .fields
            .iter()
            .any(|(_, item)| contains_guarded(builder, item, walk, visiting)),
        Ty::Param(_) => walk.param_counts,
        _ => false,
    }
}

const BUFFER_WALK: ContainsWalk = ContainsWalk {
    leaf: |_, symbol| (symbol == Symbol::RawPtr).then_some(true),
    param_counts: true,
    // Stored views own their referents (owning stored views —
    // docs/ownership-rethink-plan.md, wave E's second half): a borrowed
    // payload counts like any other stored reference.
    skip_borrowed_payloads: false,
};

const OBJECT_WALK: ContainsWalk = ContainsWalk {
    leaf: |builder, symbol| {
        builder
            .struct_def(symbol)
            .is_some_and(|(def, _)| def.heap)
            .then_some(true)
    },
    param_counts: false,
    skip_borrowed_payloads: false,
};

/// Whether this complete type application conforms to a marker protocol.
/// A specialized row is evidence only for matching arguments, never for its
/// whole nominal family, and a conditional row only where its context is
/// proven (ADR 0036).
fn conforms_to(builder: &ProgramBuilder<'_>, ty: &Ty, protocol: Symbol) -> bool {
    builder.catalog.ty_conforms(ty, &ProtocolRef::bare(protocol))
}

/// Whether dropping a value of this type does work: it owns refcounted
/// buffers, or a field does. Borrowed-conforming views own nothing.
fn needs_drop(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {
    if let Ty::Borrow(_, inner) = ty {
        return needs_drop_inner(builder, inner, true);
    }
    if let Some(&known) = builder.needs_drop_cache.borrow().get(ty) {
        return known;
    }
    let computed = needs_drop_inner(builder, ty, false);
    builder
        .needs_drop_cache
        .borrow_mut()
        .insert(ty.clone(), computed);
    computed
}

fn needs_drop_inner(builder: &ProgramBuilder<'_>, ty: &Ty, borrowed: bool) -> bool {
    if borrowed {
        return false;
    }
    match ty {
        Ty::Nominal(symbol, _) if *symbol == Symbol::RawPtr => false,
        // A `Deinit` conformance is a destructor hook: the value needs
        // its drop scheduled even when no field owns a buffer.
        Ty::Nominal(..) if conforms_to(builder, ty, Symbol::Deinit) => true,
        Ty::Nominal(_, _) => contains_buffer(builder, ty),
        // Aggregate components own even when borrow-typed (owning
        // stored views); only a top-level borrow is a frame view.
        Ty::Tuple(items) => items
            .iter()
            .any(|item| needs_drop(builder, &strip_borrows(item.clone()))),
        Ty::Record(row) => row
            .fields
            .iter()
            .any(|(_, item)| needs_drop(builder, &strip_borrows(item.clone()))),
        // An existential's payload teardown dispatches through its drop
        // witness whatever the hidden type is; a rigid effect-generic
        // value releases through the frame's witnesses (EFF-03).
        Ty::Any { .. } | Ty::Param(_) => true,
        _ => false,
    }
}

/// Whether values of this type are borrowed views: an explicit borrow, or
/// a `Borrowed`-conforming nominal (Substring, UTF8View, Character…).
/// Whether a type is, or stores anywhere, a borrowed view: the guard
/// for provenance-based escape checks (owned values carry provenance
/// for invalidation but may leave their frame freely).
fn contains_borrow_classified(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {
    if borrow_classified(builder, ty) {
        return true;
    }
    match ty {
        Ty::Tuple(items) => items
            .iter()
            .any(|item| contains_borrow_classified(builder, item)),
        Ty::Record(row) => row
            .fields
            .iter()
            .any(|(_, item)| contains_borrow_classified(builder, item)),
        Ty::Nominal(symbol, args) => {
            if let Some(fields) = builder.field_types(*symbol, args) {
                fields.iter().any(|field| borrow_classified(builder, field))
            } else if let Some(payloads) = builder.variant_payloads(*symbol, args) {
                payloads
                    .iter()
                    .flatten()
                    .any(|payload| borrow_classified(builder, payload))
            } else {
                false
            }
        }
        _ => false,
    }
}

fn borrow_classified(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {
    match ty {
        Ty::Borrow(_, _) => true,
        Ty::Nominal(..) => conforms_to(builder, ty, Symbol::Borrowed),
        _ => false,
    }
}

/// Whether values of this type are strict-linear: they must be consumed
/// exactly once on every finite path, and never implicitly dropped.
fn is_linear(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {
    match ty {
        Ty::Nominal(symbol, args) if *symbol == Symbol::InlineArray => args
            .first()
            .is_some_and(|element| is_linear(builder, element)),
        Ty::Nominal(symbol, _) => {
            builder
                .struct_def(*symbol)
                .is_some_and(|(def, _)| def.linear)
                || builder.enum_def(*symbol).is_some_and(|(def, _)| def.linear)
        }
        Ty::Tuple(items) => items.iter().any(|item| is_linear(builder, item)),
        Ty::Record(row) => row.fields.iter().any(|(_, item)| is_linear(builder, item)),
        _ => false,
    }
}

fn head_args(ty: &Ty) -> &[Ty] {
    match ty {
        Ty::Nominal(_, args) => args,
        _ => &[],
    }
}

/// Whether values of this type can carry `'heap` object handles anywhere.
/// Whether donating a reference to this type requires structural work:
/// it owns refcounted buffers or region-claimed objects somewhere.
/// `retain_value` is the one owner of that work (buffers retain, heap
/// handles acquire region claims, enums dispatch on their tag).
fn donates(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {
    contains_buffer(builder, ty) || contains_object(builder, ty)
}

fn contains_object(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {
    if let Some(&known) = builder.contains_object_cache.borrow().get(ty) {
        return known;
    }
    let computed = contains_guarded(builder, ty, &OBJECT_WALK, &mut Vec::new());
    builder
        .contains_object_cache
        .borrow_mut()
        .insert(ty.clone(), computed);
    computed
}

fn mem_ty_of(ty: &Ty) -> MemTy {
    let mut ty = ty;
    while let Ty::Borrow(_, inner) = ty {
        ty = inner;
    }
    if let Ty::Nominal(symbol, args) = ty
        && args.is_empty()
    {
        if *symbol == Symbol::Byte {
            return MemTy::Byte;
        }
        if *symbol == Symbol::Int {
            return MemTy::I64;
        }
        if *symbol == Symbol::Float {
            return MemTy::F64;
        }
        if *symbol == Symbol::Bool {
            return MemTy::Bool;
        }
        if *symbol == Symbol::RawPtr {
            return MemTy::Ptr;
        }
    }
    MemTy::Boxed
}

/// Locals of the enclosing function that a nested body reads: every
/// resolved variable use minus what the body itself binds. Order is first
/// use (deterministic environments).
fn free_locals(nodes: &[&Node], enclosing: &FxHashMap<Symbol, LocalId>) -> Vec<Symbol> {
    use derive_visitor::{Drive, Visitor};
    #[derive(Visitor)]
    #[visitor(
        Expr(enter),
        Pattern(enter),
        Decl(enter),
        crate::typed_ast::Parameter(enter)
    )]
    struct Collect<'e> {
        enclosing: &'e FxHashMap<Symbol, LocalId>,
        bound: Vec<Symbol>,
        free: Vec<Symbol>,
    }
    impl Collect<'_> {
        fn enter_expr(&mut self, expr: &Expr) {
            if let ExprKind::Variable(Name::Resolved(symbol, _)) = &expr.kind
                && self.enclosing.contains_key(symbol)
                && !self.bound.contains(symbol)
                && !self.free.contains(symbol)
            {
                self.free.push(*symbol);
            }
        }
        fn enter_pattern(&mut self, pattern: &Pattern) {
            if let PatternKind::Bind(Name::Resolved(symbol, _)) = &pattern.kind {
                self.bound.push(*symbol);
            }
        }
        fn enter_decl(&mut self, _decl: &Decl) {}
        fn enter_parameter(&mut self, param: &crate::typed_ast::Parameter) {
            if let Name::Resolved(symbol, _) = &param.name {
                self.bound.push(*symbol);
            }
        }
    }
    let mut collect = Collect {
        enclosing,
        bound: Vec::new(),
        free: Vec::new(),
    };
    for node in nodes {
        match node {
            Node::Expr(expr) => expr.drive(&mut collect),
            Node::Stmt(stmt) => stmt.drive(&mut collect),
            Node::Decl(decl) => decl.drive(&mut collect),
        }
    }
    collect.free
}

/// Find a frame's assignment-converted symbols: assigned anywhere in the
/// frame (including from inside a nested function value) and referenced
/// under a nested function value. Their bindings become cells so the
/// frame and its closures share one mutable slot — assignment conversion
/// (Kranz et al., ORBIT, SIGPLAN 1986). Returns `(celled, nested_refs)`;
/// the second set feeds the letrec decision for local function binders.
fn cell_scan(
    nodes: &[&Node],
) -> (
    rustc_hash::FxHashSet<Symbol>,
    rustc_hash::FxHashSet<Symbol>,
    FxHashMap<Symbol, usize>,
) {
    use derive_visitor::{Drive, Visitor};
    #[derive(Visitor)]
    #[visitor(Expr(enter, exit), Decl(enter, exit), Stmt(enter))]
    struct Scan {
        depth: usize,
        assigned: rustc_hash::FxHashSet<Symbol>,
        nested: rustc_hash::FxHashSet<Symbol>,
        // Frame-level (depth 0) variable use counts: the liveness
        // source for last-use borrow tracking.
        uses: FxHashMap<Symbol, usize>,
    }
    impl Scan {
        fn enter_expr(&mut self, expr: &Expr) {
            if matches!(expr.kind, ExprKind::Func(_)) {
                self.depth += 1;
            } else if let ExprKind::Variable(Name::Resolved(symbol, _)) = &expr.kind {
                if self.depth > 0 {
                    self.nested.insert(*symbol);
                } else {
                    *self.uses.entry(*symbol).or_insert(0) += 1;
                }
            }
        }
        fn exit_expr(&mut self, expr: &Expr) {
            if matches!(expr.kind, ExprKind::Func(_)) {
                self.depth -= 1;
            }
        }
        fn enter_decl(&mut self, decl: &Decl) {
            // A named local function is a nested frame like a func
            // expression (its recursion reference counts as nested).
            if matches!(decl.kind, DeclKind::Func(_)) {
                self.depth += 1;
            }
        }
        fn exit_decl(&mut self, decl: &Decl) {
            if matches!(decl.kind, DeclKind::Func(_)) {
                self.depth -= 1;
            }
        }
        fn enter_stmt(&mut self, stmt: &Stmt) {
            if let StmtKind::Assignment(lhs, _) = &stmt.kind
                && let ExprKind::Variable(Name::Resolved(symbol, _)) = &lhs.kind
            {
                self.assigned.insert(*symbol);
            }
        }
    }
    let mut scan = Scan {
        depth: 0,
        assigned: rustc_hash::FxHashSet::default(),
        nested: rustc_hash::FxHashSet::default(),
        uses: FxHashMap::default(),
    };
    for node in nodes {
        match node {
            Node::Expr(expr) => expr.drive(&mut scan),
            Node::Stmt(stmt) => stmt.drive(&mut scan),
            Node::Decl(decl) => decl.drive(&mut scan),
        }
    }
    let celled = scan.assigned.intersection(&scan.nested).copied().collect();
    (celled, scan.nested, scan.uses)
}

/// The closure-environment contract, bind side (mirror of
/// `capture_env`): the nested frame's prologue reads captured values
/// back out — cell handles keep cell semantics — then the inherited
/// witness pairs and conformance dictionaries, then the captured
/// capabilities. New environment slot kinds are added here and in
/// `capture_env`, nowhere else.
fn bind_env(
    enclosing_locals: &FxHashMap<Symbol, LocalId>,
    enclosing_cells: &rustc_hash::FxHashSet<LocalId>,
    fx: &mut FunctionBuilder,
    captured: &[Symbol],
    inherited: &[(Symbol, (LocalId, LocalId))],
    effects: &[Symbol],
) {
    for (index, symbol) in captured.iter().enumerate() {
        let local = fx.fresh_local();
        fx.push(Inst::EnvGet {
            dest: local,
            index: u16::try_from(index).unwrap_or_default(),
        });
        fx.locals.insert(*symbol, local);
        fx.captured_locals.insert(local);
        if enclosing_locals
            .get(symbol)
            .is_some_and(|enclosing| enclosing_cells.contains(enclosing))
        {
            fx.cell_handles.insert(local);
        }
    }
    let mut env_index = u16::try_from(captured.len()).unwrap_or_default();
    for (param_symbol, _) in inherited.iter() {
        let drop_local = fx.fresh_local();
        fx.push(Inst::EnvGet {
            dest: drop_local,
            index: env_index,
        });
        let retain_local = fx.fresh_local();
        fx.push(Inst::EnvGet {
            dest: retain_local,
            index: env_index + 1,
        });
        env_index += 2;
        fx.param_witnesses
            .insert(*param_symbol, (drop_local, retain_local));
        for protocol in fx.program_builder.rigid_constraints(*param_symbol) {
            let count = fx
                .program_builder
                .protocol_requirements(protocol.protocol)
                .map(|requirements| requirements.len())
                .unwrap_or(0);
            let mut locals = Vec::new();
            for _ in 0..count {
                let local = fx.fresh_local();
                fx.push(Inst::EnvGet {
                    dest: local,
                    index: env_index,
                });
                env_index += 1;
                locals.push(local);
            }
            fx.param_requirements
                .insert((*param_symbol, protocol.protocol), locals);
        }
    }
    for effect in effects {
        let clause = fx.fresh_local();
        fx.push(Inst::EnvGet {
            dest: clause,
            index: env_index,
        });
        let index_local = fx.fresh_local();
        fx.push(Inst::EnvGet {
            dest: index_local,
            index: env_index + 1,
        });
        env_index += 2;
        fx.capabilities.insert(*effect, (clause, index_local));
    }
    let _ = env_index;
}

/// The binding symbols a pattern introduces paired with their component
/// types, walking the pattern and the initializer type together (Bind,
/// Tuple, and Record shapes; anything else yields nothing and stays
/// frame-local).
fn pattern_bindings_with_tys(pattern: &Pattern, ty: &Ty) -> Vec<(Symbol, Ty)> {
    match (&pattern.kind, ty) {
        (PatternKind::Bind(Name::Resolved(symbol, _)), _) => vec![(*symbol, ty.clone())],
        (PatternKind::Tuple(elements), Ty::Tuple(items)) if elements.len() == items.len() => {
            elements
                .iter()
                .zip(items)
                .flat_map(|(element, item)| pattern_bindings_with_tys(element, item))
                .collect()
        }
        (PatternKind::Record { fields }, Ty::Record(row)) => {
            let field_ty = |name: &Name| {
                row.fields.iter().find_map(|(label, ty)| match label {
                    crate::label::Label::Named(label) if *label == name.name_str() => {
                        Some(ty.clone())
                    }
                    _ => None,
                })
            };
            fields
                .iter()
                .flat_map(|field| match &field.kind {
                    RecordFieldPatternKind::Bind(name) => match (name.symbol(), field_ty(name)) {
                        (Ok(symbol), Some(ty)) => vec![(symbol, ty)],
                        _ => Vec::new(),
                    },
                    RecordFieldPatternKind::Equals { name, value } => {
                        let Some(ty) = field_ty(name) else {
                            return Vec::new();
                        };
                        let mut binds: Vec<(Symbol, Ty)> = name
                            .symbol()
                            .ok()
                            .map(|symbol| (symbol, ty.clone()))
                            .into_iter()
                            .collect();
                        binds.extend(pattern_bindings_with_tys(value, &ty));
                        binds
                    }
                    RecordFieldPatternKind::Rest => Vec::new(),
                })
                .collect()
        }
        _ => Vec::new(),
    }
}

/// The binding symbols a pattern introduces, in order. A record field
/// `label: pattern` binds the label in addition to the sub-pattern's
/// binders (the checker binds both names).
fn pattern_bind_symbols(pattern: &Pattern) -> Vec<Symbol> {
    let mut symbols = Vec::new();
    fn walk(pattern: &Pattern, symbols: &mut Vec<Symbol>) {
        match &pattern.kind {
            PatternKind::Bind(Name::Resolved(symbol, _)) => symbols.push(*symbol),
            PatternKind::Tuple(items) | PatternKind::Or(items) => {
                for item in items {
                    walk(item, symbols);
                }
            }
            PatternKind::Variant { fields, .. } => {
                for field in fields {
                    walk(field, symbols);
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(Name::Resolved(symbol, _)) => {
                            symbols.push(*symbol);
                        }
                        RecordFieldPatternKind::Equals { name, value } => {
                            if let Name::Resolved(symbol, _) = name {
                                symbols.push(*symbol);
                            }
                            walk(value, symbols);
                        }
                        _ => {}
                    }
                }
            }
            PatternKind::Struct { fields, .. } => {
                for field in fields {
                    walk(field, symbols);
                }
            }
            _ => {}
        }
    }
    walk(pattern, &mut symbols);
    symbols
}

/// A value's shape ignores how it is held: strip borrow wrappers.
fn strip_borrows(mut ty: Ty) -> Ty {
    while let Ty::Borrow(_, inner) = ty {
        ty = *inner;
    }
    ty
}

/// Component types for a positional pattern: the tuple's items when the
/// scrutinee type shows them, error placeholders otherwise.
fn tuple_element_tys(ty: &Ty, len: usize) -> Vec<Ty> {
    match strip_borrows(ty.clone()) {
        Ty::Tuple(items) => items,
        _ => vec![Ty::Error; len],
    }
}

/// One record-pattern cell per row slot, in the row's label-sorted
/// layout order (the same layout record literals build; rows fix field
/// positions — Gaster & Jones, 1996). Slots the pattern leaves to `..`
/// become wildcards, so record matching reuses the positional tuple
/// machinery below.
struct RecordCell {
    field_ty: Ty,
    /// The slot's sub-pattern: a pun's bind, `label: pattern`'s
    /// pattern, or a synthesized wildcard for an unmentioned field.
    pattern: Pattern,
    /// `label: pattern` binds the label in addition to matching the
    /// sub-pattern (the checker binds both names); `label: _` folds
    /// into a plain bind instead.
    bind: Option<Name>,
}

/// Whether a type contains an associated-type projection anywhere.
fn ty_has_projection(ty: &Ty) -> bool {
    struct Search {
        found: bool,
    }
    impl crate::types::ty::TyFold for Search {
        fn fold_ty(&mut self, ty: &Ty) -> Ty {
            if matches!(ty, Ty::Proj(_, _, _)) {
                self.found = true;
            }
            self.fold_children(ty)
        }
    }
    let mut search = Search { found: false };
    crate::types::ty::TyFold::fold_ty(&mut search, ty);
    search.found
}

/// Whether a type mentions any rigid parameter at all (a generic
/// position).
/// A resolved assignment/writeback destination: a base binding plus a
/// projection spine.
#[derive(Clone)]
struct PlaceChain {
    base: LocalId,
    global_slot: Option<u32>,
    links: Vec<PlaceLink>,
}

/// Where one evolved value from a `(result, final mut values…)` callee
/// lands.
enum WritebackTarget {
    /// Straight into its place.
    Place(PlaceChain),
    /// Rebuilt as an existential around the evolved payload first.
    Repack {
        chain: PlaceChain,
        protocol: Symbol,
        witnesses: Vec<Operand>,
    },
}

#[derive(Clone)]
struct PlaceLink {
    index: u16,
    heap: bool,
    field_ty: Ty,
    /// `Some(row width)` when the parent is a record row — runtime records
    /// are tuples, so writes rebuild the tuple instead of `SetField`.
    record_arity: Option<u16>,
}

/// The distinct rigid effect-generic parameters a substitution's types
/// mention, in first-appearance order. A callee instance whose types
/// mention rigid params receives one hidden `[drop, retain]` witness pair
/// per entry, appended by every caller in this order — the sub-dictionary
/// rule of Go's generics dictionaries (Griesemer et al., OOPSLA 2022) and
/// the value-witness-table model of Swift's unspecialized-generics ABI.
/// The symbols of a parameter list's TYPE-kind entries — the generics
/// that carry runtime values and therefore witness blocks.
fn type_param_symbols(params: &[crate::types::ty::SchemeParam]) -> Vec<Symbol> {
    params
        .iter()
        .filter(|param| matches!(param.kind, crate::types::ty::ParamKind::Type))
        .map(|param| param.symbol)
        .collect()
}

fn witness_params(subst: &[(Symbol, Ty)]) -> Vec<Symbol> {
    fn walk(ty: &Ty, out: &mut Vec<Symbol>) {
        match ty {
            Ty::Param(symbol) => {
                if !out.contains(symbol) {
                    out.push(*symbol);
                }
            }
            Ty::Borrow(_, inner) => walk(inner, out),
            Ty::Tuple(items) => {
                for item in items {
                    walk(item, out);
                }
            }
            Ty::Record(row) => {
                for (_, item) in &row.fields {
                    walk(item, out);
                }
            }
            Ty::Nominal(_, args) => {
                for arg in args {
                    walk(arg, out);
                }
            }
            Ty::Func(params, ret, _) => {
                for param in params {
                    walk(param, out);
                }
                walk(ret, out);
            }
            Ty::Any { protocol, .. } => {
                for arg in &protocol.args {
                    walk(arg, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    for (_, ty) in subst {
        walk(ty, &mut out);
    }
    out
}

/// The rigid effect-generics one type mentions, in the deterministic
/// order glue chunks and their MakeClosure sites share.
fn glue_witness_params(ty: &Ty) -> Vec<Symbol> {
    witness_params(std::slice::from_ref(&(Symbol::RawPtr, ty.clone())))
}

/// Solve one effect generic from a declared parameter shape matched
/// against the perform's concrete argument type (first-order structural
/// matching; the checker already proved the shapes agree).
fn solve_param(declared: &Ty, concrete: &Ty, generic: Symbol) -> Option<Ty> {
    match (declared, concrete) {
        (Ty::Param(param), _) if *param == generic => Some(concrete.clone()),
        (Ty::Borrow(_, a), Ty::Borrow(_, b)) => solve_param(a, b, generic),
        (Ty::Tuple(a), Ty::Tuple(b)) => a
            .iter()
            .zip(b)
            .find_map(|(x, y)| solve_param(x, y, generic)),
        (Ty::Nominal(_, a), Ty::Nominal(_, b)) => a
            .iter()
            .zip(b)
            .find_map(|(x, y)| solve_param(x, y, generic)),
        (Ty::Func(pa, ra, _), Ty::Func(pb, rb, _)) => pa
            .iter()
            .zip(pb)
            .find_map(|(x, y)| solve_param(x, y, generic))
            .or_else(|| solve_param(ra, rb, generic)),
        _ => None,
    }
}

/// Whether a type contains a solver variable anywhere.
fn ty_has_var(ty: &Ty) -> bool {
    struct Search {
        found: bool,
    }
    impl crate::types::ty::TyFold for Search {
        fn fold_var(&mut self, var: crate::types::ty::TyVar) -> Ty {
            self.found = true;
            Ty::Var(var)
        }
    }
    let mut search = Search { found: false };
    crate::types::ty::TyFold::fold_ty(&mut search, ty);
    search.found
}

/// Whether a type mentions a rigid parameter symbol (`Self` is
/// `Ty::Param(protocol symbol)`), comparing canonically against the
/// owning module.
fn ty_mentions_param(ty: &Ty, symbol: Symbol, module: crate::compiling::module::ModuleId) -> bool {
    struct Search {
        symbol: Symbol,
        module: crate::compiling::module::ModuleId,
        found: bool,
    }
    impl crate::types::ty::TyFold for Search {
        fn fold_param(&mut self, param: Symbol) -> Ty {
            if param == self.symbol || canonical(param, self.module) == self.symbol {
                self.found = true;
            }
            Ty::Param(param)
        }
    }
    let mut search = Search {
        symbol,
        module,
        found: false,
    };
    crate::types::ty::TyFold::fold_ty(&mut search, ty);
    search.found
}

/// Symbols are minted module-local (`Current`) and retagged on import.
/// Canonicalizing against the owning program's module identity makes one
/// symbol mean one callable across the whole graph.
/// Canonicalize every symbol inside a type against its owning program's
/// module identity (the type-level counterpart of [`canonical`]).
fn canonical_ty(ty: &Ty, module: crate::compiling::module::ModuleId) -> Ty {
    struct Retag {
        module: crate::compiling::module::ModuleId,
    }
    impl crate::types::ty::TyFold for Retag {
        fn fold_symbol(&mut self, symbol: Symbol) -> Symbol {
            canonical(symbol, self.module)
        }
        fn fold_param(&mut self, param: Symbol) -> Ty {
            // Scheme type parameters keep their identity across the
            // import seam (instantiation maps address them directly);
            // protocol `Self` params are module symbols and retag.
            if matches!(param, Symbol::TypeParameter(_)) {
                Ty::Param(param)
            } else {
                Ty::Param(canonical(param, self.module))
            }
        }
    }
    if module == crate::compiling::module::ModuleId::Current {
        return ty.clone();
    }
    crate::types::ty::TyFold::fold_ty(&mut Retag { module }, ty)
}

thread_local! {
    /// Local-module-id aliases for the compile in progress: one module can
    /// carry several local ids in an environment (a direct import and a
    /// re-export); the frontend unifies them by stable id, and this table
    /// collapses every alias onto one canonical local id for the backend.
    /// A flat table indexed by module id — `canonical` runs on every
    /// tagged symbol the backend touches, and hashing here was measurable
    /// against the whole compile.
    static MODULE_ALIASES: std::cell::RefCell<Vec<u16>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Install the alias map for the duration of a compile (the returned guard
/// clears it).
pub(crate) fn module_alias_scope(aliases: FxHashMap<u16, u16>) -> ModuleAliasGuard {
    let size = aliases
        .keys()
        .copied()
        .max()
        .map(|module| usize::from(module) + 1)
        .unwrap_or(0);
    let mut table: Vec<u16> = (0..u16::try_from(size).unwrap_or(u16::MAX)).collect();
    for (from, to) in aliases {
        table[usize::from(from)] = to;
    }
    MODULE_ALIASES.with(|slot| *slot.borrow_mut() = table);
    ModuleAliasGuard
}

pub(crate) struct ModuleAliasGuard;

impl Drop for ModuleAliasGuard {
    fn drop(&mut self) {
        MODULE_ALIASES.with(|slot| slot.borrow_mut().clear());
    }
}

pub(crate) fn canonical(symbol: Symbol, module: crate::compiling::module::ModuleId) -> Symbol {
    use crate::compiling::module::ModuleId;
    let symbol = if module != ModuleId::Current && symbol.module_id() == Some(ModuleId::Current) {
        symbol.import(module)
    } else {
        symbol
    };
    match symbol.module_id() {
        Some(tagged) if tagged != ModuleId::Current => {
            MODULE_ALIASES.with(|slot| match slot.borrow().get(usize::from(tagged.0)) {
                Some(&unified) if unified != tagged.0 => {
                    symbol.import(crate::compiling::module::ModuleId(unified))
                }
                _ => symbol,
            })
        }
        _ => symbol,
    }
}

pub(crate) fn build(programs: &[ProgramInput<'_>], entry: Entry) -> Result<Program, BackendError> {
    unsafe_gate::check(programs)?;
    let mut builder = ProgramBuilder::new(programs);
    builder.index_callables();

    // Stored positions cannot hold borrows (CHG-04's storage face): a
    // struct field or enum payload typed as a borrow would outlive its
    // loan. Borrowed-classified view types are the exemption — the
    // view IS the loan.
    let user = &programs[0];
    for (declared, def) in &user.program.types().catalog.structs {
        let symbol = canonical(*declared, user.module);
        if builder
            .catalog
            .family_unconditionally_conforms(symbol, Symbol::Borrowed)
        {
            continue;
        }
        for (name, (_, field_ty)) in &def.fields {
            if matches!(field_ty, Ty::Borrow(_, _)) {
                return Err(BackendError::new(
                    format!("a borrowed value cannot be stored in struct field `{name}`"),
                    Span::SYNTHESIZED,
                ));
            }
        }
    }
    for (declared, def) in &user.program.types().catalog.enums {
        let symbol = canonical(*declared, user.module);
        if builder
            .catalog
            .family_unconditionally_conforms(symbol, Symbol::Borrowed)
        {
            continue;
        }
        for variant in def.variants.values() {
            if let Ty::Func(payloads, _, _) = &variant.constructor_scheme.ty {
                for payload in payloads {
                    if matches!(payload, Ty::Borrow(_, _)) {
                        return Err(BackendError::new(
                            "a borrowed value cannot be stored in an enum payload".into(),
                            Span::SYNTHESIZED,
                        ));
                    }
                }
            }
        }
    }

    let check_all = std::env::var_os("TALK_CHECK_ALL").is_some();
    let entry_result = match entry {
        Entry::Named(name) => builder.build_named_entry(name),
        Entry::Script => builder.build_script_entry(),
    };
    let entry_id = match entry_result {
        Ok(id) => id,
        // In check mode a declaration-only program still checks: the
        // entry is an empty function and every callable compiles below.
        Err(error) if check_all && error.message.contains("nothing to run") => {
            let id = builder.reserve("empty_entry");
            let fx = FunctionBuilder::new(&mut builder, 0, 0);
            let (n_locals, blocks) = fx.finish(Operand::Const(Constant::Unit))?;
            builder.functions[id] = Function {
                name: "empty_entry".into(),
                arity: 0,
                n_locals,
                blocks,
            };
            id
        }
        Err(error) => return Err(error),
    };
    // TALK_CHECK_ALL: also compile every user-program callable, called
    // or not — the reference's flow pass checked every declaration,
    // while demand-driven compilation checks what runs. Generic
    // callables compile rigidly (each scheme parameter bound to
    // itself), exercising the witness machinery.
    if check_all {
        let user: Vec<(Symbol, Vec<(Symbol, Ty)>)> = builder
            .callables
            .iter()
            .filter(|(_, callable)| callable.program == 0)
            .map(|(symbol, callable)| {
                let mut subst: Vec<(Symbol, Ty)> = callable
                    .body
                    .scheme_params()
                    .iter()
                    .map(|param| (param.symbol, Ty::Param(param.symbol)))
                    .collect();
                // Owner parameters range over member bodies too (a
                // static one is a value, ADR 0035 §6); bind them rigidly
                // the way a concrete receiver's instantiation (or a
                // conformance's selected application) binds them. The
                // protocol Self entry is the evidence marker
                // `demand_specialized` keys on.
                if let Some(params) = builder.method_owner_params(*symbol) {
                    subst.extend(params.into_iter().map(|param| (param, Ty::Param(param))));
                }
                if let Some(owner) = builder.default_owner_protocol(*symbol) {
                    subst.push((owner, Ty::Param(owner)));
                    if let Some(params) = builder.protocol_params(owner) {
                        subst.extend(params.into_iter().map(|param| (param, Ty::Param(param))));
                    }
                }
                (*symbol, subst)
            })
            .collect();
        for (symbol, subst) in user {
            builder.demand(symbol, subst, Span::SYNTHESIZED)?;
        }
    }
    builder.drain_worklist()?;

    Ok(Program {
        functions: builder.functions,
        entry: entry_id,
        global_slots: u32::try_from(builder.global_slots.len()).unwrap_or_default(),
    })
}

/// A monomorphic function instance: a callable symbol plus the concrete
/// types substituted for its scheme parameters (whole-program
/// monomorphization in the MLton/TIL sense).
type Instance = (Symbol, Vec<(Symbol, Ty)>);

/// Compiler-generated value glue for existential witness tables.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Glue {
    Drop,
    Retain,
    /// A `'heap` struct's finalizer body: Deinit hook, then
    /// buffer-field frees (the region walk frees the object slots).
    HeapTeardown,
}

struct ProgramBuilder<'a> {
    programs: &'a [ProgramInput<'a>],
    /// Every program's catalog, canonicalized and merged: the one table
    /// associated-type projections normalize through.
    catalog: crate::types::catalog::TypeCatalog,
    callables: FxHashMap<Symbol, Callable<'a>>,
    /// Top-level `let` initializer expressions, by binding symbol. Literal
    /// initializers of dependency programs inline at read sites.
    globals: FxHashMap<Symbol, (&'a Expr, usize)>,
    /// The root program's top-level bindings get real static slots,
    /// initialized in order by the script entry (LINK-02): symbol → slot.
    global_slots: FxHashMap<Symbol, u32>,
    /// Declared types of global slots (for replacement drops).
    global_tys: FxHashMap<u32, Ty>,
    functions: Vec<Function>,
    func_ids: FxHashMap<Instance, FuncId>,
    /// Hidden witness parameters per instance, in append order: rigid
    /// effect-generics the instance's substitution mentions.
    instance_witnesses: FxHashMap<FuncId, Vec<Symbol>>,
    /// Writeback tuple widths per compiled instance, checked against
    /// every caller's expectation after the worklist drains: a
    /// convention mismatch is a compile error, never silent skew.
    writeback_widths: FxHashMap<FuncId, usize>,
    writeback_expectations: Vec<(FuncId, usize, Span)>,
    last_writeback_width: usize,
    worklist: Vec<(Instance, FuncId)>,
    /// Synthesized drop/retain glue chunks, one per payload type.
    glue: FxHashMap<(Ty, Glue), FuncId>,
    /// Synthesized structural-equality chunks per type: the checker
    /// derives `Equatable` for enums, structs, and tuples with no source
    /// body, so the backend supplies one (field/payload-wise, dispatching
    /// to real conformances at nominal leaves).
    equality_glue: FxHashMap<Ty, FuncId>,
    /// Synthesized `show` chunks for checker-derived `Showable`
    /// conformances: enums render `Name.variant(payloads…)`, structs
    /// `Name(field: value…)` — the archived synthesis format.
    show_glue: FxHashMap<Ty, FuncId>,
    /// Canonical-symbol indexes over every program's catalog, built once:
    /// the per-query alternative (scan all programs, canonicalizing every
    /// key) is quadratic in catalog size and dominated large compiles.
    struct_index: FxHashMap<
        Symbol,
        (
            &'a crate::types::catalog::StructInfo,
            crate::compiling::module::ModuleId,
        ),
    >,
    enum_index: FxHashMap<
        Symbol,
        (
            &'a crate::types::catalog::Enum,
            crate::compiling::module::ModuleId,
        ),
    >,
    variant_index: FxHashMap<Symbol, (Symbol, u16)>,
    /// Every canonical `deinit` witness symbol (a hook's own `self`
    /// binding must not re-dispatch the hook on scope exit).
    deinit_witnesses: rustc_hash::FxHashSet<Symbol>,
    /// Memoized structural type queries: drop emission asks these per
    /// field per site, and the answers depend only on the (fixed)
    /// catalogs.
    needs_drop_cache: std::cell::RefCell<FxHashMap<Ty, bool>>,
    contains_buffer_cache: std::cell::RefCell<FxHashMap<Ty, bool>>,
    contains_object_cache: std::cell::RefCell<FxHashMap<Ty, bool>>,
}

impl<'a> ProgramBuilder<'a> {
    fn new(programs: &'a [ProgramInput<'a>]) -> Self {
        let mut catalog = crate::types::catalog::TypeCatalog::default();
        for input in programs {
            let canonicalized = input
                .program
                .types()
                .catalog
                .clone()
                .import_as(input.module);
            catalog.merge(canonicalized);
        }
        let mut struct_index: FxHashMap<
            Symbol,
            (
                &'a crate::types::catalog::StructInfo,
                crate::compiling::module::ModuleId,
            ),
        > = FxHashMap::default();
        let mut enum_index: FxHashMap<
            Symbol,
            (
                &'a crate::types::catalog::Enum,
                crate::compiling::module::ModuleId,
            ),
        > = FxHashMap::default();
        let mut variant_index: FxHashMap<Symbol, (Symbol, u16)> = FxHashMap::default();
        let deinit_witnesses: rustc_hash::FxHashSet<Symbol> = catalog
            .conformances
            .values()
            .filter(|row| row.protocol.protocol == Symbol::Deinit)
            .filter_map(|row| row.witnesses.get("deinit").copied())
            .collect();
        for input in programs {
            let source = &input.program.types().catalog;
            for (declared, def) in &source.structs {
                struct_index
                    .entry(canonical(*declared, input.module))
                    .or_insert((def, input.module));
            }
            for (declared, def) in &source.enums {
                let enum_symbol = canonical(*declared, input.module);
                enum_index.entry(enum_symbol).or_insert((def, input.module));
                for (tag, (_, case)) in def.variants.iter().enumerate() {
                    variant_index
                        .entry(canonical(case.symbol, input.module))
                        .or_insert((enum_symbol, u16::try_from(tag).unwrap_or_default()));
                }
            }
        }
        Self {
            programs,
            catalog,
            struct_index,
            enum_index,
            variant_index,
            deinit_witnesses,
            needs_drop_cache: std::cell::RefCell::new(FxHashMap::default()),
            contains_buffer_cache: std::cell::RefCell::new(FxHashMap::default()),
            contains_object_cache: std::cell::RefCell::new(FxHashMap::default()),
            callables: FxHashMap::default(),
            globals: FxHashMap::default(),
            global_slots: FxHashMap::default(),
            global_tys: FxHashMap::default(),
            functions: Vec::new(),
            func_ids: FxHashMap::default(),
            instance_witnesses: FxHashMap::default(),
            writeback_widths: FxHashMap::default(),
            writeback_expectations: Vec::new(),
            last_writeback_width: 0,
            worklist: Vec::new(),
            glue: FxHashMap::default(),
            equality_glue: FxHashMap::default(),
            show_glue: FxHashMap::default(),
        }
    }

    /// Walk every program's typed roots and record each function or method
    /// body by its canonical symbol. Named `func` declarations in a script
    /// surface as expression nodes; they are declarations here too.
    fn index_callables(&mut self) {
        for (program_ix, input) in self.programs.iter().enumerate() {
            for file in input.program.files().values() {
                for node in &file.roots {
                    match node {
                        Node::Decl(decl) => {
                            if let Some((bound, func)) = let_bound_func(decl) {
                                self.index_bound_func(bound, func, program_ix);
                            } else {
                                if let DeclKind::Let {
                                    lhs:
                                        Pattern {
                                            kind: PatternKind::Bind(Name::Resolved(symbol, _)),
                                            ..
                                        },
                                    rhs: Some(rhs),
                                    ..
                                } = &decl.kind
                                {
                                    let symbol =
                                        canonical(*symbol, self.programs[program_ix].module);
                                    self.globals.insert(symbol, (rhs, program_ix));
                                }
                                self.index_decl(decl, program_ix);
                            }
                        }
                        Node::Expr(Expr {
                            kind: ExprKind::Func(func),
                            ..
                        }) => {
                            self.index_func(func, program_ix);
                        }
                        Node::Stmt(Stmt {
                            kind:
                                StmtKind::Expr(Expr {
                                    kind: ExprKind::Func(func),
                                    ..
                                }),
                            ..
                        }) => self.index_func(func, program_ix),
                        _ => {}
                    }
                }
            }
        }
    }

    fn index_decl(&mut self, decl: &'a Decl, program_ix: usize) {
        match &decl.kind {
            DeclKind::Func(func) => self.index_func(func, program_ix),
            DeclKind::Method {
                func,
                receiver_mode,
                ..
            } => self.index_method(func, program_ix, *receiver_mode),
            DeclKind::Init {
                name: Name::Resolved(symbol, _),
                params,
                body,
            } => {
                let symbol = canonical(*symbol, self.programs[program_ix].module);
                self.callables.insert(
                    symbol,
                    Callable {
                        body: CallableBody::Init { params, body },
                        program: program_ix,
                        receiver: crate::node_kinds::decl::ReceiverMode::None,
                    },
                );
            }
            DeclKind::Struct { body, .. }
            | DeclKind::Protocol { body, .. }
            | DeclKind::Extend { body, .. }
            | DeclKind::Enum { body, .. } => {
                for member in &body.decls {
                    self.index_decl(member, program_ix);
                }
            }
            _ => {}
        }
    }

    fn index_func(&mut self, func: &'a Func, program: usize) {
        self.index_method(func, program, crate::node_kinds::decl::ReceiverMode::None)
    }

    /// Nested `func` declarations index like top-level ones, so calls to
    /// them — including self-recursion — resolve to a compiled body.
    /// Capture-free nested functions execute; capturing ones keep their
    /// explicit rejection when their body compiles.
    fn index_nested_funcs(&mut self, block: &'a Block, program: usize) {
        for node in &block.body {
            match node {
                Node::Decl(decl) => match &decl.kind {
                    DeclKind::Func(func) => self.index_func(func, program),
                    DeclKind::Let { rhs: Some(rhs), .. } => self.index_nested_expr(rhs, program),
                    _ => {}
                },
                Node::Stmt(stmt) => self.index_nested_stmt(stmt, program),
                Node::Expr(expr) => self.index_nested_expr(expr, program),
            }
        }
    }

    fn index_nested_stmt(&mut self, stmt: &'a Stmt, program: usize) {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.index_nested_expr(expr, program),
            StmtKind::If(cond, then_block, else_block) => {
                self.index_nested_expr(cond, program);
                self.index_nested_funcs(then_block, program);
                if let Some(else_block) = else_block {
                    self.index_nested_funcs(else_block, program);
                }
            }
            StmtKind::Return(Some(expr)) | StmtKind::Resume(Some(expr)) => {
                self.index_nested_expr(expr, program)
            }
            StmtKind::Assignment(target, value) => {
                self.index_nested_expr(target, program);
                self.index_nested_expr(value, program);
            }
            StmtKind::Loop(cond, body) => {
                if let Some(cond) = cond {
                    self.index_nested_expr(cond, program);
                }
                self.index_nested_funcs(body, program);
            }
            StmtKind::Handling { body, .. } => self.index_nested_funcs(body, program),
            StmtKind::Return(None)
            | StmtKind::Resume(None)
            | StmtKind::Continue
            | StmtKind::Break => {}
        }
    }

    fn index_nested_expr(&mut self, expr: &'a Expr, program: usize) {
        match &expr.kind {
            ExprKind::Func(func) => self.index_func(func, program),
            ExprKind::Block(block) | ExprKind::Unsafe(block) => {
                self.index_nested_funcs(block, program)
            }
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
                for item in items {
                    self.index_nested_expr(item, program);
                }
            }
            ExprKind::Call { callee, args, .. } => {
                self.index_nested_expr(callee, program);
                for arg in args {
                    self.index_nested_expr(&arg.value, program);
                }
            }
            ExprKind::CallEffect { args, .. } => {
                for arg in args {
                    self.index_nested_expr(&arg.value, program);
                }
            }
            ExprKind::Con { args, .. } => {
                for arg in args {
                    self.index_nested_expr(arg, program);
                }
            }
            ExprKind::Clone(inner) | ExprKind::Proj(inner, _, _) => {
                self.index_nested_expr(inner, program)
            }
            ExprKind::Member(receiver, _) => {
                if let Some(receiver) = receiver {
                    self.index_nested_expr(receiver, program);
                }
            }
            ExprKind::Match(scrutinee, arms) => {
                self.index_nested_expr(scrutinee, program);
                for arm in arms {
                    self.index_nested_funcs(&arm.body, program);
                }
            }
            ExprKind::RecordLiteral { fields, spread } => {
                for field in fields {
                    self.index_nested_expr(&field.value, program);
                }
                if let Some(spread) = spread {
                    self.index_nested_expr(spread, program);
                }
            }
            ExprKind::InlineIR(instruction) => {
                for bind in &instruction.binds {
                    self.index_nested_expr(bind, program);
                }
            }
            ExprKind::Lit(_)
            | ExprKind::Variable(_)
            | ExprKind::Constructor(_)
            | ExprKind::Temp(_) => {}
        }
    }

    fn index_method(
        &mut self,
        func: &'a Func,
        program: usize,
        receiver: crate::node_kinds::decl::ReceiverMode,
    ) {
        if let Name::Resolved(symbol, _) = &func.name {
            let symbol = canonical(*symbol, self.programs[program].module);
            self.callables.insert(
                symbol,
                Callable {
                    body: CallableBody::Func(func),
                    program,
                    receiver,
                },
            );
        }
        self.index_nested_funcs(&func.body, program);
    }

    /// Index a `let name = <func>` declaration under both the binding
    /// symbol (what calls resolve to) and the function's own symbol.
    fn index_bound_func(&mut self, bound: &Name, func: &'a Func, program: usize) {
        if let Name::Resolved(symbol, _) = bound {
            let symbol = canonical(*symbol, self.programs[program].module);
            self.callables.insert(
                symbol,
                Callable {
                    body: CallableBody::Func(func),
                    program,
                    receiver: crate::node_kinds::decl::ReceiverMode::None,
                },
            );
        }
        self.index_func(func, program);
    }

    fn reserve(&mut self, name: &str) -> FuncId {
        let id = self.functions.len();
        self.functions.push(Function {
            name: name.into(),
            arity: 0,
            n_locals: 0,
            blocks: Vec::new(),
        });
        id
    }

    /// Assign (or return) the function id for a callee instance, queueing
    /// its body for compilation. The substitution is pruned to the scheme
    /// parameters the callee actually quantifies, so a monomorphic function
    /// has exactly one instance.
    fn demand(
        &mut self,
        symbol: Symbol,
        subst: Vec<(Symbol, Ty)>,
        span: Span,
    ) -> Result<FuncId, BackendError> {
        let Some(callable) = self.callables.get(&symbol).copied() else {
            let name = self
                .programs
                .iter()
                .find_map(|input| {
                    input.program.resolved_names().symbol_names.iter().find_map(
                        |(candidate, name)| {
                            (canonical(*candidate, input.module) == symbol).then(|| name.clone())
                        },
                    )
                })
                .unwrap_or_else(|| format!("{symbol:?}"));
            return Err(BackendError::unsupported(
                format!("calls to `{name}` without an available source body are not supported yet"),
                span,
            ));
        };
        let callee_module = self.programs[callable.program].module;
        // Protocol parameters are conformance evidence exactly like
        // associated types: a default body reads the owner's `static N`
        // as a value (ADR 0035 §6) though it never shows in the method's
        // own scheme. The call site binds the selected application's
        // arguments under a `Symbol::Protocol` Self entry; keep that
        // protocol's parameters through the pruning.
        let evidence_params: rustc_hash::FxHashSet<Symbol> = subst
            .iter()
            .filter(|(param, _)| matches!(param, Symbol::Protocol(_)))
            .flat_map(|(protocol, _)| self.protocol_params(*protocol).unwrap_or_default())
            .collect();
        let mut subst: Vec<(Symbol, Ty)> = subst
            .into_iter()
            .filter(|(param, _)| match callable.body {
                // Initializer bodies range over their struct's parameters,
                // which have no scheme of their own.
                CallableBody::Init { .. } => true,
                CallableBody::Func(_) => {
                    // Associated-type bindings are conformance evidence:
                    // they appear in default bodies without showing in the
                    // scheme, so pruning keeps them unconditionally.
                    matches!(param, Symbol::AssociatedType(_))
                        || evidence_params.contains(param)
                        || callable.body.scheme_params().iter().any(|scheme_param| {
                            canonical(scheme_param.symbol, callee_module) == *param
                                || scheme_param.symbol == *param
                        })
                        || callable
                            .body
                            .scheme_ty()
                            .is_some_and(|ty| ty_mentions_param(ty, *param, callee_module))
                }
            })
            .collect();
        subst.sort_by_key(|(param, _)| *param);
        let instance = (symbol, subst);
        if let Some(id) = self.func_ids.get(&instance).copied() {
            return Ok(id);
        }
        let id = self.reserve(&callable.body.name());
        self.func_ids.insert(instance.clone(), id);
        // Recorded at reserve time so callers can append witness args
        // before the instance body compiles off the worklist.
        self.instance_witnesses
            .insert(id, witness_params(&instance.1));
        self.worklist.push((instance, id));
        Ok(id)
    }

    /// The one deferred-selection point (ADR 0036): dereference a concrete
    /// self type's conformance to its implementation symbol through the
    /// catalog's shared instance matcher. Typing commits everything
    /// decidable at typing time (`MemberResolution::ViaConformance`); this
    /// serves the remainder — requirement operations whose receiver became
    /// concrete only under an instance substitution, and compiler-owned
    /// glue. Coherence makes the lookup forced, so it cannot disagree with
    /// the frontend.
    fn conformance_witness(
        &self,
        self_ty: &Ty,
        protocol: &crate::types::ty::ProtocolRef,
        label: &crate::label::Label,
    ) -> Option<(Symbol, Vec<(Symbol, Ty)>)> {
        let mut self_ty = self_ty;
        while let Ty::Borrow(_, inner) = self_ty {
            self_ty = inner;
        }
        let Ty::Nominal(self_head, self_args) = self_ty else {
            return None;
        };
        let crate::label::Label::Named(label) = label else {
            return None;
        };

        let matches = self
            .catalog
            .satisfied_conformances(*self_head, self_args, protocol);
        let [selected] = matches.as_slice() else {
            return None;
        };
        let witness = selected.conformance.witnesses.get(label).copied()?;
        let mut subst = selected
            .substitution
            .clone()
            .into_iter()
            .collect::<Vec<_>>();
        for (assoc, bound) in &selected.conformance.assoc {
            subst.push((
                *assoc,
                bound.substitute(
                    &selected.substitution,
                    &FxHashMap::default(),
                    &FxHashMap::default(),
                ),
            ));
        }
        Some((witness, subst))
    }

    /// The associated-type bindings a conformance row supplies for this
    /// self type: `(assoc symbol, bound type)` with the row's rigid
    /// parameters instantiated against the application's arguments. A
    /// protocol default body's substitution needs these alongside `Self`
    /// (an unresolved associated type otherwise survives as a rigid
    /// param).
    fn conformance_assoc(
        &self,
        self_ty: &Ty,
        protocol: &crate::types::ty::ProtocolRef,
    ) -> Vec<(Symbol, Ty)> {
        let mut self_ty = self_ty;
        while let Ty::Borrow(_, inner) = self_ty {
            self_ty = inner;
        }
        let Ty::Nominal(self_head, self_args) = self_ty else {
            return Vec::new();
        };
        let matches = self
            .catalog
            .satisfied_conformances(*self_head, self_args, protocol);
        let [matched] = matches.as_slice() else {
            return Vec::new();
        };
        matched
            .conformance
            .assoc
            .iter()
            .map(|(assoc, bound)| {
                (
                    *assoc,
                    bound.substitute(
                        &matched.substitution,
                        &FxHashMap::default(),
                        &FxHashMap::default(),
                    ),
                )
            })
            .collect()
    }

    /// The enum declaration behind a canonical symbol, from whichever
    /// program's catalog declares it.
    fn enum_def(
        &self,
        symbol: Symbol,
    ) -> Option<(
        &'a crate::types::catalog::Enum,
        crate::compiling::module::ModuleId,
    )> {
        self.enum_index.get(&symbol).copied()
    }

    /// The struct declaration behind a canonical symbol.
    fn struct_def(
        &self,
        symbol: Symbol,
    ) -> Option<(
        &'a crate::types::catalog::StructInfo,
        crate::compiling::module::ModuleId,
    )> {
        self.struct_index.get(&symbol).copied()
    }

    /// A struct's stored field types, canonicalized and instantiated
    /// against the application's type arguments.
    fn field_types(&self, symbol: Symbol, args: &[Ty]) -> Option<Vec<Ty>> {
        if symbol == Symbol::InlineArray
            && let [element, count] = args
        {
            let count = match count {
                Ty::Static(StaticValue::Int(value)) if value.as_i64().is_some() => value
                    .as_i64()
                    .and_then(|value| usize::try_from(value).ok())
                    .filter(|value| *value <= usize::from(u16::MAX)),
                // Check-all compilation keeps static parameters rigid. One
                // representative element is enough for structural ownership;
                // reachable instances always carry a concrete count.
                Ty::Param(_) | Ty::Static(StaticValue::Int(_)) => Some(1),
                _ => None,
            }?;
            return Some(vec![element.clone(); count]);
        }
        let (def, module) = self.struct_def(symbol)?;
        // Raw keys for the same reason as `variant_payloads`.
        let substitution: FxHashMap<Symbol, Ty> = def
            .params
            .iter()
            .map(|param| param.symbol)
            .zip(args.iter().cloned())
            .collect();
        Some(
            def.fields
                .values()
                .map(|(_, ty)| {
                    canonical_ty(ty, module).substitute(
                        &substitution,
                        &FxHashMap::default(),
                        &FxHashMap::default(),
                    )
                })
                .collect(),
        )
    }

    /// The declaration-order index of a stored field, by its source name.
    fn field_index_by_name(&self, struct_symbol: Symbol, name: &str) -> Option<u16> {
        let (def, _) = self.struct_def(struct_symbol)?;
        def.fields
            .keys()
            .position(|field| field == name)
            .and_then(|index| u16::try_from(index).ok())
    }

    /// The declaration-order index of a stored field, by its property
    /// symbol.
    fn field_index(&self, struct_symbol: Symbol, field: Symbol) -> Option<u16> {
        let (def, module) = self.struct_def(struct_symbol)?;
        def.fields
            .values()
            .position(|(property, _)| canonical(*property, module) == field)
            .and_then(|index| u16::try_from(index).ok())
    }

    /// The enum and declaration-order tag that a resolved variant symbol
    /// belongs to.
    fn variant_tag(&self, variant: Symbol) -> Option<(Symbol, u16)> {
        self.variant_index.get(&variant).copied()
    }

    /// Each variant's payload types for an enum application, in tag order.
    fn variant_payloads(&self, symbol: Symbol, args: &[Ty]) -> Option<Vec<Vec<Ty>>> {
        let (def, module) = self.enum_def(symbol)?;
        // Substitution keys stay raw: `canonical_ty` keeps `Ty::Param`
        // symbols as authored (core params are owner-stamped at creation),
        // so a re-stamped key would never match its occurrences.
        let substitution: FxHashMap<Symbol, Ty> = def
            .params
            .iter()
            .map(|param| param.symbol)
            .zip(args.iter().cloned())
            .collect();
        Some(
            def.variants
                .values()
                .map(|variant| match &variant.constructor_scheme.ty {
                    Ty::Func(params, _, _) => params
                        .iter()
                        .map(|param| {
                            canonical_ty(param, module).substitute(
                                &substitution,
                                &FxHashMap::default(),
                                &FxHashMap::default(),
                            )
                        })
                        .collect(),
                    _ => Vec::new(),
                })
                .collect(),
        )
    }

    /// The `Deinit` hook for a nominal application, with the substitution
    /// binding the conformance row's rigid parameters against it.
    fn deinit_witness(&self, head: Symbol, args: &[Ty]) -> Option<(Symbol, Vec<(Symbol, Ty)>)> {
        let matches =
            self.catalog
                .satisfied_conformances(head, args, &ProtocolRef::bare(Symbol::Deinit));
        let [matched] = matches.as_slice() else {
            return None;
        };
        let witness = matched.conformance.witnesses.get("deinit").copied()?;
        Some((witness, matched.substitution.clone().into_iter().collect()))
    }

    /// Whether this callable IS some type's `deinit` hook: its own `self`
    /// binding must not re-dispatch the hook on scope exit.
    fn is_deinit_witness(&self, symbol: Symbol) -> bool {
        self.deinit_witnesses.contains(&symbol)
    }

    /// Whether this type's teardown routes through one shared drop
    /// function per program instead of expanding at every drop site
    /// (the per-type `dec` shape — Ullrich & de Moura, IFL 2019;
    /// Perceus, PLDI 2021, presumes it before selectively re-inlining).
    /// Shared when the expansion is big enough to be worth a call: an
    /// enum's tag dispatch, or a struct/tuple/record with a destructor
    /// hook or at least two owned fields. Never shared: rigid-generic
    /// glue (its sites hold the frame witnesses), linear types (their
    /// drops are diagnosed errors at the site), and `'heap` structs
    /// (their site drop is a single region release).
    fn drop_is_shared(&self, ty: &Ty) -> bool {
        if !glue_witness_params(ty).is_empty() || is_linear(self, ty) {
            return false;
        }
        let dropping = |items: &mut dyn Iterator<Item = &Ty>| {
            items
                .filter(|item| {
                    matches!(item, Ty::Nominal(head, _) if *head == Symbol::RawPtr)
                        || needs_drop(self, item)
                })
                .count()
        };
        match ty {
            Ty::Nominal(symbol, args) => {
                if self.enum_index.contains_key(symbol) {
                    return true;
                }
                let Some((def, _)) = self.struct_def(*symbol) else {
                    return false;
                };
                if def.heap {
                    return false;
                }
                let Some(fields) = self.field_types(*symbol, args) else {
                    return false;
                };
                !self
                    .catalog
                    .satisfied_conformances(*symbol, args, &ProtocolRef::bare(Symbol::Deinit))
                    .is_empty()
                    || dropping(&mut fields.iter()) >= 2
            }
            Ty::Tuple(items) => dropping(&mut items.iter()) >= 2,
            Ty::Record(row) => dropping(&mut row.fields.iter().map(|(_, item)| item)) >= 2,
            _ => false,
        }
    }

    /// An effect's signature from the input catalogs, with the owning
    /// module. Signatures here keep their authored symbols: rigid params
    /// stay raw (matching `Ty::Param` occurrences in resolved types, which
    /// never re-stamp), while nominal types canonicalize against the
    /// returned module at use sites.
    fn effect_sig(
        &self,
        effect: Symbol,
    ) -> Option<(
        &'a crate::types::catalog::EffectSig,
        crate::compiling::module::ModuleId,
    )> {
        for input in self.programs {
            for (declared, sig) in &input.program.types().catalog.effects {
                if canonical(*declared, input.module) == effect {
                    return Some((sig, input.module));
                }
            }
        }
        None
    }

    /// Conformance constraints on one rigid generic (raw symbol, as it
    /// appears in `Ty::Param` occurrences): the frontend-published
    /// declared bounds (`TypeCatalog::param_bounds` — typing publishes,
    /// lowering reads), expanded through transitive protocol supers.
    /// These decide the protocol-dictionary layout of the rigid's hidden
    /// witness block, so every bind/forward/inherit site derives from
    /// this one answer (Wadler & Blott, POPL 1989).
    fn rigid_constraints(&self, param: Symbol) -> Vec<crate::types::ty::ProtocolRef> {
        // The merged catalog keys by imported symbol; a raw module-local
        // param resolves through its program's canonical form (the same
        // two spellings `demand`'s subst filter accepts).
        let bounds = self.catalog.param_bounds.get(&param).or_else(|| {
            self.programs.iter().find_map(|input| {
                self.catalog
                    .param_bounds
                    .get(&canonical(param, input.module))
            })
        });
        let mut expanded: Vec<crate::types::ty::ProtocolRef> = Vec::new();
        for bound in bounds.into_iter().flatten() {
            for protocol in self.catalog.protocol_and_supers(bound) {
                if !expanded.iter().any(|seen| seen.protocol == protocol.protocol) {
                    expanded.push(protocol);
                }
            }
        }
        expanded
    }

    /// A type's display name, for derived rendering.
    fn display_name(&self, symbol: Symbol) -> String {
        self.programs
            .iter()
            .find_map(|input| {
                input
                    .program
                    .resolved_names()
                    .symbol_names
                    .iter()
                    .find_map(|(candidate, name)| {
                        (canonical(*candidate, input.module) == symbol).then(|| name.clone())
                    })
            })
            .unwrap_or_else(|| format!("{symbol:?}"))
    }

    /// A protocol from the reachable graph by display name (`Add` for the
    /// derived-show concatenation witness).
    fn protocol_named(&self, name: &str) -> Option<Symbol> {
        for input in self.programs {
            let names = input.program.resolved_names();
            for protocol in input.program.types().catalog.protocols.keys() {
                if names
                    .symbol_names
                    .get(protocol)
                    .is_some_and(|candidate| candidate == name)
                {
                    return Some(canonical(*protocol, input.module));
                }
            }
        }
        None
    }

    /// The enum variant names for a nominal, in tag order.
    fn variant_names(&self, symbol: Symbol) -> Option<Vec<String>> {
        for input in self.programs {
            let catalog = &input.program.types().catalog;
            for (declared, info) in &catalog.enums {
                if canonical(*declared, input.module) == symbol {
                    return Some(info.variants.keys().cloned().collect());
                }
            }
        }
        None
    }

    /// The struct field names for a nominal, in declaration order.
    fn field_names(&self, symbol: Symbol) -> Option<Vec<String>> {
        for input in self.programs {
            let catalog = &input.program.types().catalog;
            for (declared, info) in &catalog.structs {
                if canonical(*declared, input.module) == symbol {
                    return Some(info.fields.keys().cloned().collect());
                }
            }
        }
        None
    }

    /// Synthesize `(self) -> String` for a checker-derived `Showable`
    /// conformance.
    fn derived_show(
        &mut self,
        ty: &Ty,
        protocol: &crate::types::ty::ProtocolRef,
        span: Span,
    ) -> Result<FuncId, BackendError> {
        if let Some(id) = self.show_glue.get(ty) {
            return Ok(*id);
        }
        let id = self.reserve("derived_show");
        self.show_glue.insert(ty.clone(), id);
        let mut fx = FunctionBuilder::new(self, 1, 0);
        let result = fx.emit_show(Operand::Local(0), ty, protocol, span)?;
        let (n_locals, blocks) = fx.finish(result)?;
        self.functions[id] = Function {
            name: "derived_show".into(),
            arity: 1,
            n_locals,
            blocks,
        };
        Ok(id)
    }

    /// Synthesize `(a, b) -> Bool` structural equality for a type whose
    /// `Equatable` conformance the checker derived (no source body).
    fn derived_equality(
        &mut self,
        ty: &Ty,
        protocol: &crate::types::ty::ProtocolRef,
        span: Span,
    ) -> Result<FuncId, BackendError> {
        if let Some(id) = self.equality_glue.get(ty) {
            return Ok(*id);
        }
        let id = self.reserve("derived_equals");
        self.equality_glue.insert(ty.clone(), id);
        let mut fx = FunctionBuilder::new(self, 2, 0);
        let result = fx.emit_equality(Operand::Local(0), Operand::Local(1), ty, protocol, span)?;
        let (n_locals, blocks) = fx.finish(result)?;
        self.functions[id] = Function {
            name: "derived_equals".into(),
            arity: 2,
            n_locals,
            blocks,
        };
        Ok(id)
    }

    /// A protocol's requirement labels in declaration order (witness-table
    /// slot order, after the two fixed slots).
    fn protocol_requirements(&self, protocol: Symbol) -> Option<Vec<String>> {
        self.catalog
            .protocols
            .get(&protocol)
            .map(|info| info.requirements.keys().cloned().collect())
    }

    /// The requirement symbol behind a protocol's labeled requirement.
    fn requirement_symbol(&self, protocol: Symbol, label: &str) -> Option<Symbol> {
        for input in self.programs {
            let catalog = &input.program.types().catalog;
            for (declared, info) in &catalog.protocols {
                if canonical(*declared, input.module) != protocol {
                    continue;
                }
                if let Some(requirement) = info.requirements.get(label) {
                    return Some(canonical(requirement.symbol, input.module));
                }
            }
        }
        None
    }

    /// Whether this effect symbol is core's `'io` (the runtime's
    /// implicitly handled host-IO effect).
    fn is_io_effect(&self, effect: Symbol) -> bool {
        if effect.module_id() != Some(crate::compiling::module::ModuleId::Core) {
            return false;
        }
        self.programs.iter().any(|input| {
            input
                .program
                .resolved_names()
                .symbol_names
                .iter()
                .any(|(symbol, name)| {
                    name == "io"
                        && matches!(symbol, Symbol::Effect(_))
                        && canonical(*symbol, input.module) == effect
                })
        })
    }

    /// The protocol's input parameter symbols, from whichever program's
    /// catalog declares it.
    /// The declared value type of a static parameter (ADR 0035), from
    /// whichever program's catalog registered it. `param` may be raw or
    /// canonical.
    fn static_param_domain(&self, param: Symbol) -> Option<Ty> {
        for input in self.programs {
            let catalog = &input.program.types().catalog;
            for (declared, ty) in &catalog.static_params {
                if *declared == param || canonical(*declared, input.module) == param {
                    return Some(canonical_ty(ty, input.module));
                }
            }
        }
        None
    }

    /// The declared parameters of the nominal whose member table owns
    /// this method or initializer, if any — rigid check-mode compilation
    /// binds them the way a concrete receiver's instantiation would.
    fn method_owner_params(&self, symbol: Symbol) -> Option<Vec<Symbol>> {
        for input in self.programs {
            let catalog = &input.program.types().catalog;
            let matches =
                |member: Symbol| member == symbol || canonical(member, input.module) == symbol;
            let owner_params = |params: &[crate::types::ty::SchemeParam]| {
                params
                    .iter()
                    .map(|param| canonical(param.symbol, input.module))
                    .collect()
            };
            for info in catalog.structs.values() {
                if info
                    .methods
                    .values()
                    .chain(info.statics.values())
                    .copied()
                    .chain(info.inits.iter().map(|(init, _)| *init))
                    .any(matches)
                {
                    return Some(owner_params(&info.params));
                }
            }
            for info in catalog.enums.values() {
                if info.methods.values().copied().any(matches) {
                    return Some(owner_params(&info.params));
                }
            }
            // Inherent extend members carry their own rigid params (the
            // instance-head binders).
            for members in catalog.extend_members.values() {
                for rows in members.values() {
                    for row in rows {
                        if matches(row.symbol) {
                            return Some(
                                row.params
                                    .iter()
                                    .map(|param| canonical(*param, input.module))
                                    .collect(),
                            );
                        }
                    }
                }
            }
        }
        None
    }

    /// The protocol whose requirement table owns this default body, if
    /// any — rigid check-mode compilation binds the owner's parameters
    /// the way a conformance's selected application would.
    fn default_owner_protocol(&self, symbol: Symbol) -> Option<Symbol> {
        for input in self.programs {
            let catalog = &input.program.types().catalog;
            for (declared, info) in &catalog.protocols {
                if info
                    .requirements
                    .values()
                    .any(|requirement| canonical(requirement.symbol, input.module) == symbol)
                {
                    return Some(canonical(*declared, input.module));
                }
            }
        }
        None
    }

    fn protocol_params(&self, protocol: Symbol) -> Option<Vec<Symbol>> {
        for input in self.programs {
            let catalog = &input.program.types().catalog;
            for (declared, info) in &catalog.protocols {
                if canonical(*declared, input.module) == protocol {
                    return Some(
                        info.params
                            .iter()
                            .map(|param| canonical(param.symbol, input.module))
                            .collect(),
                    );
                }
            }
        }
        None
    }

    fn drain_worklist(&mut self) -> Result<(), BackendError> {
        while let Some(((symbol, subst), id)) = self.worklist.pop() {
            let callable = self.callables[&symbol];
            let suppress_self_drop = self.is_deinit_witness(symbol);
            let func = self.compile_func(callable, &subst, suppress_self_drop)?;
            self.writeback_widths.insert(id, self.last_writeback_width);
            self.functions[id] = func;
        }
        // Cross-check the convention: every caller's expected writeback
        // width against the callee instance's actual one.
        for (func, expected, span) in std::mem::take(&mut self.writeback_expectations) {
            let actual = self.writeback_widths.get(&func).copied().unwrap_or(0);
            if expected != actual {
                let name = self
                    .functions
                    .get(func)
                    .map(|function| function.name.clone())
                    .unwrap_or_else(|| "?".into());
                return Err(BackendError::new(
                    format!(
                        "writeback convention mismatch: caller expects {expected} evolved values, `{name}` returns {actual}"
                    ),
                    span,
                ));
            }
        }
        Ok(())
    }

    fn compile_func(
        &mut self,
        callable: Callable<'a>,
        subst: &[(Symbol, Ty)],
        suppress_self_drop: bool,
    ) -> Result<Function, BackendError> {
        let (name, params, body) = match callable.body {
            CallableBody::Func(func) => {
                if !func.captures.is_empty() {
                    return Err(BackendError::unsupported(
                        format!(
                            "captures on `{}` are not supported yet",
                            func.name.name_str()
                        ),
                        func.body.span,
                    ));
                }
                (func.name.name_str(), &func.params[..], &func.body)
            }
            CallableBody::Init { params, body } => ("init".into(), params, body),
        };

        let declared_arity = u16::try_from(params.len())
            .map_err(|_| BackendError::new("too many parameters".into(), body.span))?;
        // Hidden witness parameters follow the declared ones: one
        // [drop, retain] pair per rigid effect-generic this instance's
        // substitution mentions. Callers append them in the same order
        // (recorded in `instance_witnesses` at demand time).
        let hidden = witness_params(subst);
        let mut fx = FunctionBuilder::new(self, declared_arity, callable.program);
        fx.flow_label = name.clone();
        let arity = fx.bind_witness_params(&hidden, declared_arity);
        fx.next_local = arity;
        fx.subst = subst.iter().cloned().collect();
        fx.in_init = matches!(callable.body, CallableBody::Init { .. });
        if let CallableBody::Func(func) = callable.body
            && let Ty::Func(_, ret, _) = &func.scheme.ty
        {
            let ret = fx.resolved(ret);
            // Only a bare `&T` return is a view-return now: a marked
            // nominal (Substring, an iterator) owns its referent and
            // donates at the return like any other value.
            fx.returns_borrow = matches!(&ret, Ty::Borrow(_, _));
            fx.return_ty = Some(ret);
        }
        // The caller reconstructs this order from the same rule: `mut`
        // receiver first, then `mut` (exclusive-borrow) parameters in
        // declaration order. Initializers are exempt: they return their
        // receiver, never a writeback tuple (constructions do not
        // unpack), and their borrow parameters mutate through the
        // borrow itself.
        fx.consuming_receiver = matches!(
            callable.receiver,
            crate::node_kinds::decl::ReceiverMode::Consuming
        );
        fx.param_floor = declared_arity;
        if !fx.in_init {
            if matches!(
                callable.receiver,
                crate::node_kinds::decl::ReceiverMode::Ref
            ) {
                fx.writeback_params.push(0);
            }
            for (ix, param) in params.iter().enumerate() {
                let local = u16::try_from(ix).unwrap_or_default();
                if let Some(ty) = &param.ty
                    && matches!(fx.resolved(ty), Ty::Borrow(Perm::Exclusive, _))
                    && !fx.writeback_params.contains(&local)
                {
                    fx.writeback_params.push(local);
                }
            }
        }
        for (ix, param) in params.iter().enumerate() {
            let local = u16::try_from(ix).unwrap_or_default();
            if let Some(ty) = &param.ty {
                if matches!(ty, Ty::Unique(_)) {
                    fx.unique_locals.insert(local);
                }
                let ty = fx.resolved(ty);
                fx.local_tys.insert(local, ty.clone());
                fx.check_copy(&ty, body.span)?;
                // Owned (non-borrow) parameters are the callee's to drop —
                // except a deinit body's own `self`, whose teardown the
                // caller glue owns.
                if !(suppress_self_drop && ix == 0) {
                    fx.own_local(local, &ty);
                }
            }
            if let Name::Resolved(symbol, _) = &param.name {
                fx.locals.insert(*symbol, local);
            }
        }

        // Assignment conversion: mutable locals shared with closures
        // become cells; celled parameters re-bind through a cell.
        let body_nodes: Vec<&Node> = body.body.iter().collect();
        let (celled, nested_refs, use_counts) = cell_scan(&body_nodes);
        fx.celled = celled;
        fx.nested_refs = nested_refs;
        fx.use_counts = use_counts;
        fx.cell_celled_params(params);

        let width = fx.writeback_params.len();
        fx.program_builder.last_writeback_width = width;
        let value = fx.compile_block(body)?;
        // An initializer returns its (fully assigned) receiver whether or
        // not the body ends with `self`.
        let value = match callable.body {
            CallableBody::Init { .. } => Operand::Local(0),
            CallableBody::Func(_) => value,
        };
        let (n_locals, blocks) = fx.finish(value)?;
        Ok(Function {
            name,
            arity,
            n_locals,
            blocks,
        })
    }
}

/// One compiled control-flow arm awaiting its join: where it ended, its
/// value, and the ownership state it finished with.
/// One live borrow: the view symbol (for liveness), its display name,
/// the owner's local, and whether the loan is exclusive.
struct Loan {
    view_symbol: Symbol,
    view_name: String,
    root: LocalId,
    exclusive: bool,
    /// Loop depth at creation: inside a deeper loop the view's uses
    /// recur with the iterations, so the loan stays live through the
    /// whole loop whatever the syntactic use count says (liveness over
    /// back edges — the non-lexical-lifetimes lesson, RFC 2094).
    loop_depth: usize,
}

struct ArmEnd {
    block: BlockId,
    value: Operand,
    moved: rustc_hash::FxHashSet<LocalId>,
    moved_globals: rustc_hash::FxHashSet<u32>,
    temps: Vec<LocalId>,
}

/// What a loop's `break`/`continue` jump to, and how many scopes stay
/// live across the jump.
struct LoopFrame {
    header: BlockId,
    /// Moved state at each `continue`, unioned into the back-edge for
    /// loop-carried move detection.
    continues_moved: rustc_hash::FxHashSet<LocalId>,
    /// Each `break`'s end state, merged at the loop exit exactly like
    /// if-arms merge at their join (a local moved on one break path
    /// drops on every other path that still owns it).
    breaks: Vec<ArmEnd>,
}

struct FunctionBuilder<'p, 'a> {
    program_builder: &'p mut ProgramBuilder<'a>,
    /// The `TypeOutput` side tables of the program this body came from.
    program: usize,
    /// This instance's scheme-parameter substitution: baked node types in
    /// the body resolve through it before any scalar decision.
    subst: FxHashMap<Symbol, Ty>,
    locals: FxHashMap<Symbol, LocalId>,
    next_local: u16,
    blocks: Vec<BlockData>,
    current: BlockId,
    loop_stack: Vec<LoopFrame>,
    /// Lexical scopes of droppable owned locals, in declaration order
    /// (structural drops, ADR 0017/0030).
    scopes: Vec<Vec<LocalId>>,
    /// The declared type of every tracked owned local or temp.
    owned_tys: FxHashMap<LocalId, Ty>,
    /// Locals whose value moved out (no scope-exit drop).
    moved: rustc_hash::FxHashSet<LocalId>,
    /// Owned rvalue temporaries of the statement being compiled; they drop
    /// at the statement boundary unless a consumer takes them.
    stmt_temps: Vec<LocalId>,
    /// Suppress old-value drops for `self.field =` inside an initializer:
    /// the fresh record's placeholders are not values.
    in_init: bool,
    /// A `mut func` receiver writes back through the private tuple-return
    /// convention: every return wraps `(result, final self)`.
    writeback_params: Vec<LocalId>,
    /// This frame's `[drop, retain]` witness locals per rigid
    /// effect-generic: from the perform site in clause bodies, from hidden
    /// parameters in rigid-substituted instances.
    param_witnesses: rustc_hash::FxHashMap<Symbol, (LocalId, LocalId)>,
    /// Requirement-implementation closures per (rigid generic, constraint
    /// protocol), in the protocol's requirement order — the frame's
    /// conformance dictionaries.
    param_requirements: rustc_hash::FxHashMap<(Symbol, Symbol), Vec<LocalId>>,
    /// Locals holding environment copies of enclosing-frame bindings.
    /// Writing one would mutate the copy, not the binding, so assignments
    /// to them fail closed.
    captured_locals: rustc_hash::FxHashSet<LocalId>,
    /// Symbols this frame assignment-converts to cells (see `cell_scan`).
    celled: rustc_hash::FxHashSet<Symbol>,
    /// Symbols referenced under a nested function value in this frame —
    /// the letrec test for local function binders.
    nested_refs: rustc_hash::FxHashSet<Symbol>,
    /// Locals holding cell handles: reads go through CellGet, writes
    /// through CellSet, and captures pass the (copyable) handle.
    cell_handles: rustc_hash::FxHashSet<LocalId>,
    /// Globals whose values were consumed (moved) in this frame: later
    /// reads reject until a reassignment restores them.
    moved_globals: rustc_hash::FxHashSet<u32>,
    /// Borrow provenance: a view maps to the frame local it derives
    /// from, so moving or reassigning the owner invalidates the view
    /// and returning it out of the owning frame rejects.
    borrow_roots: FxHashMap<LocalId, LocalId>,
    /// Views whose owner moved or was reassigned: reads reject.
    invalidated_views: rustc_hash::FxHashSet<LocalId>,
    /// Locals whose type is itself a borrowed view: the only ones
    /// invalidation can strike (owned donations carry provenance for
    /// chain derivation but own their copies).
    view_locals: rustc_hash::FxHashSet<LocalId>,
    /// Frame-level variable use counts, decremented at each compiled
    /// read: a loan is live while its view has uses remaining
    /// (last-use liveness, RFC 2094's model in source order).
    use_counts: FxHashMap<Symbol, usize>,
    /// Live loans: reading a mut-borrowed owner, mutating a
    /// shared-borrowed one, or moving any borrowed owner rejects while
    /// the loan is live.
    loans: Vec<Loan>,
    /// The frame's declared result type: returns donate references for
    /// place reads the frame does not own, like any owned sink.
    return_ty: Option<Ty>,
    /// This frame is a `consuming func`: dropping its receiver is the
    /// sanctioned end of the value's life (linear disposal included).
    consuming_receiver: bool,
    /// Locals below this are declared parameters: dropping an owned
    /// (consume-marked) parameter is the callee's sanctioned disposal.
    param_floor: u16,
    /// Set while building a shared drop function: the body's root value
    /// must expand structurally (routing it back through the shared
    /// function would call itself forever); nested occurrences of the
    /// same type are real recursion and do share.
    drop_glue_root: Option<Ty>,
    /// Scrutinee local → its tag local, scoped to one `match`
    /// compilation: every arm tests the same scrutinee, and later arm
    /// tests are only reachable on paths where no arm body has run,
    /// so one `GetTag` serves the whole match.
    match_tag_cache: FxHashMap<LocalId, LocalId>,
    /// The frame's unwind cleanup chain, outermost value first: each
    /// node's block drops one live value and jumps toward the outermost,
    /// which ends the walk with `UnwindRet`. Call sites reuse the chain
    /// as long as the live set below them is unchanged; a consumed
    /// mid-stack value invalidates only the nodes above it. Sound
    /// without runtime drop flags because `merge_arms` reconciles moves
    /// at every join — the owned live set is path-independent.
    /// Building an abort-unwind cleanup block: exceptional teardown may
    /// drop linear values (the abort IS their consumption).
    in_unwind_cleanup: bool,
    /// Captured capabilities: per user effect, the creation site's
    /// handler `(clause, index)` read from this closure's environment
    /// (Effekt-style lexical capture — ADR 0011 departure (d)).
    capabilities: FxHashMap<Symbol, (LocalId, LocalId)>,
    /// Inside a handler clause: the local holding the delimiter
    /// continuation. `continue v` resumes (returns from the clause); the
    /// clause's finite value discontinues through this.
    clause_delimiter: Option<LocalId>,
    /// Locals holding values read from global slots (for mut-receiver
    /// writebacks and move guards).
    global_loads: FxHashMap<LocalId, u32>,
    /// Declared types of typed locals (params and bindings), for capture
    /// checking.
    local_tys: FxHashMap<LocalId, Ty>,
    /// Errors raised on paths that cannot return `Result` (drop emission);
    /// surfaced when the function finishes.
    deferred_errors: Vec<BackendError>,
    /// The ownership event log the balance verifier replays (wave B of
    /// docs/ownership-rethink-plan.md): one record per Def/Use/Move/Drop
    /// decision, at the block position where it was made.
    flow_events: Vec<verify::FlowRecord>,
    /// Names the function in balance-verifier reports.
    flow_label: String,
    /// The loop depth at which each tracked local was registered:
    /// consuming a value bound outside the current loop retains (the
    /// loop may repeat), whatever the syntactic use count says.
    owned_loop_depth: FxHashMap<LocalId, usize>,
    /// Locals declared unique (`*T`). The representation strips
    /// uniqueness, but sharing one would break the sole-reference
    /// contract, so they keep move semantics.
    unique_locals: rustc_hash::FxHashSet<LocalId>,
    /// A return-position consume always moves: this path ends here, so
    /// stale use counts and live views never justify a retain (the
    /// scope drops that follow skip moved values, and sibling paths
    /// keep their own state).
    in_return_consume: bool,
    /// This function returns a borrowed view: returning one of its own
    /// owned locals would let the loan escape its owner (CHG-04).
    returns_borrow: bool,
}

impl<'p, 'a> FunctionBuilder<'p, 'a> {
    fn new(program_builder: &'p mut ProgramBuilder<'a>, arity: u16, program: usize) -> Self {
        Self {
            program_builder,
            program,
            subst: FxHashMap::default(),
            locals: FxHashMap::default(),
            next_local: arity,
            blocks: vec![BlockData::default()],
            current: 0,
            loop_stack: Vec::new(),
            scopes: vec![Vec::new()],
            owned_tys: FxHashMap::default(),
            moved: rustc_hash::FxHashSet::default(),
            stmt_temps: Vec::new(),
            in_init: false,
            writeback_params: Vec::new(),
            param_witnesses: rustc_hash::FxHashMap::default(),
            param_requirements: rustc_hash::FxHashMap::default(),
            captured_locals: rustc_hash::FxHashSet::default(),
            celled: rustc_hash::FxHashSet::default(),
            nested_refs: rustc_hash::FxHashSet::default(),
            cell_handles: rustc_hash::FxHashSet::default(),
            capabilities: FxHashMap::default(),
            moved_globals: rustc_hash::FxHashSet::default(),
            borrow_roots: FxHashMap::default(),
            invalidated_views: rustc_hash::FxHashSet::default(),
            view_locals: rustc_hash::FxHashSet::default(),
            use_counts: FxHashMap::default(),
            loans: Vec::new(),
            return_ty: None,
            consuming_receiver: false,
            param_floor: 0,
            drop_glue_root: None,
            match_tag_cache: FxHashMap::default(),
            in_unwind_cleanup: false,
            clause_delimiter: None,
            global_loads: FxHashMap::default(),
            local_tys: FxHashMap::default(),
            deferred_errors: Vec::new(),
            flow_events: Vec::new(),
            flow_label: "mir".into(),
            owned_loop_depth: FxHashMap::default(),
            unique_locals: rustc_hash::FxHashSet::default(),
            in_return_consume: false,
            returns_borrow: false,
        }
    }

    /// Log an ownership decision at the current build position for the
    /// balance verifier. A terminated block discards instructions in
    /// [`Self::push`]; the log mirrors that, or post-return flushes
    /// would record drops that were never emitted.
    fn record_flow(&mut self, event: verify::FlowEvent) {
        if self.terminated() {
            return;
        }
        self.flow_events.push(verify::FlowRecord {
            block: self.current,
            index: self.blocks[self.current].insts.len() as u32,
            event,
        });
    }

    /// Emit the planned releases. Unwind chains first (their call
    /// positions index instruction vectors that entry relocation would
    /// move — though patched fields travel with their instructions),
    /// then end-of-block releases (appends, index-stable), then entry
    /// releases (which relocate a block's body into a continuation and
    /// remap its events).
    fn emit_plan(&mut self, plan: &release::Plan) {
        // Chain nodes form a trie keyed by (value, rest-of-chain):
        // nested owned sets share their common tails, so a frame whose
        // live sets only grow keeps a single UnwindRet like the old
        // prefix-healed chains did.
        let mut nodes: FxHashMap<(LocalId, Option<BlockId>), BlockId> = FxHashMap::default();
        for ((block, index), owned) in &plan.unwind_live {
            let saved = self.current;
            self.in_unwind_cleanup = true;
            let mut next: Option<BlockId> = None;
            for local in owned.iter().copied() {
                let node = match nodes.get(&(local, next)) {
                    Some(node) => *node,
                    None => {
                        let node = self.new_block();
                        self.switch_to(node);
                        self.release_planned(local);
                        match next {
                            Some(outer) => self.terminate(Term::Goto(outer, Vec::new())),
                            None => self.terminate(Term::UnwindRet),
                        }
                        nodes.insert((local, next), node);
                        node
                    }
                };
                next = Some(node);
            }
            self.in_unwind_cleanup = false;
            self.switch_to(saved);
            let head = next.unwrap_or(self.current);
            if let Inst::Call { unwind, .. } | Inst::CallIndirect { unwind, .. } =
                &mut self.blocks[*block].insts[*index as usize]
            {
                *unwind = Some(head);
            }
        }
        for (block, locals) in plan.end_of_block.iter().enumerate() {
            if locals.is_empty() {
                continue;
            }
            let Some(term) = self.blocks[block].term.take() else {
                continue;
            };
            self.switch_to(block);
            for local in locals {
                self.release_planned(*local);
            }
            self.terminate(term);
        }
        for (from, position, locals) in &plan.edges {
            // Split the edge: a fresh block releases and continues to
            // the original successor, carrying the original edge's
            // arguments (operands of the source block, still in their
            // registers when the split block runs).
            let edge = self.new_block();
            let (old_target, old_args) = match &mut self.blocks[*from].term {
                Some(Term::Goto(target, args)) => {
                    let old = (*target, std::mem::take(args));
                    *target = edge;
                    old
                }
                Some(Term::Branch {
                    then_block,
                    else_block,
                    ..
                }) => {
                    let slot = if *position == 0 {
                        then_block
                    } else {
                        else_block
                    };
                    let old = (*slot, Vec::new());
                    *slot = edge;
                    old
                }
                _ => continue,
            };
            self.switch_to(edge);
            for local in locals {
                self.release_planned(*local);
            }
            self.terminate(Term::Goto(old_target, old_args));
        }
    }

    /// One planned release: the local's tracked type, dropped where the
    /// planner decided, with the event the verifier replays.
    fn release_planned(&mut self, local: LocalId) {
        let Some(ty) = self.owned_tys.get(&local).cloned() else {
            return;
        };
        self.record_flow(verify::FlowEvent::Drop(local));
        self.drop_value(Operand::Local(local), &ty);
    }

    /// Surface any error raised during drop emission (linearity).
    fn deferred_error(&mut self) -> Result<(), BackendError> {
        match self.deferred_errors.pop() {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    fn finish(mut self, value: Operand) -> Result<(u16, Vec<BlockData>), BackendError> {
        if !self.terminated() {
            self.emit_return(value);
        }
        self.elaborate_and_verify();
        self.deferred_error()?;
        Ok((self.next_local, self.blocks))
    }

    /// Plan and emit the control-flow releases (docs/ownership-rethink-
    /// plan.md, drop elaboration), then — in debug builds — replay the
    /// combined event log through the balance verifier: the planner's
    /// output must satisfy the same checker the hand-threaded emission
    /// did. Point releases were already placed by their expressions.
    #[cfg_attr(
        debug_assertions,
        expect(
            clippy::panic,
            reason = "a broken release balance is a compiler bug: crashing \
                      the debug build with the full event log and rendered \
                      MIR is the verifier doing its job"
        )
    )]
    fn elaborate_and_verify(&mut self) {
        let plan = release::plan(&self.blocks, &self.flow_events);
        self.emit_plan(&plan);
        #[cfg(debug_assertions)]
        if self.deferred_errors.is_empty() {
            let errors = verify::check(&self.blocks, &self.flow_events, &self.flow_label);
            if !errors.is_empty() {
                let trace: Vec<String> = self
                    .flow_events
                    .iter()
                    .map(|record| format!("{record:?}"))
                    .collect();
                let rendered = Program {
                    functions: vec![Function {
                        name: self.flow_label.clone(),
                        arity: 0,
                        n_locals: self.next_local,
                        blocks: self.blocks.clone(),
                    }],
                    entry: 0,
                    global_slots: 0,
                }
                .render();
                panic!(
                    "ownership balance broken:\n{}\nevents:\n{}\n{rendered}",
                    errors.join("\n"),
                    trace.join("\n")
                );
            }
        }
    }

    /// Drop every live owned local (all scopes, reverse declaration order)
    /// except the returned value, then return. `mut` receivers and `mut`
    /// parameters return `(result, final values…)` for the caller's
    /// writeback.
    fn emit_return(&mut self, value: Operand) {
        if let Some(delimiter) = self.clause_delimiter {
            self.emit_discontinue(Operand::Local(delimiter), value);
        } else {
            self.emit_frame_return(value);
        }
    }

    fn emit_frame_return(&mut self, value: Operand) {
        // A bare `&T` return is the one value that cannot carry
        // ownership out of the frame: it has no owning representation
        // on the caller's side, so a loan of this frame's own data
        // would dangle the moment the frame's releases run (CHG-04 —
        // the surviving must-reject of the escape family, checked
        // through provenance so call results and views of locals are
        // caught, not just direct bindings). Marked view nominals
        // donate instead and left this check behind.
        if self.returns_borrow
            && let Operand::Local(view) = value
        {
            // Provenance is checked against named owned bindings only:
            // unnamed intermediates alias parameter interiors (core's
            // raw accessors), and an owned alias of a caller's value is
            // not an escape.
            let root = self.borrow_root(view);
            let named_owned = |local: LocalId| {
                self.locals.values().any(|bound| *bound == local)
                    && self.owned_tys.contains_key(&local)
                    && !self.moved.contains(&local)
            };
            if named_owned(root) || named_owned(view) {
                self.deferred_errors.push(BackendError::new(
                    format!(
                        "a borrowed return may not escape the returning frame's own value (it is owned by this function; in {})",
                        self.flow_label
                    ),
                    Span::SYNTHESIZED,
                ));
            }
        }
        // A returned place read the frame does not own donates a
        // reference, exactly like a call or construction argument. An
        // escaping view carries its own retain now (owning stored
        // views), so the old provenance rejection has no job left. Core
        // sources stay exempt for their manual buffer code (`_load`,
        // `_alloc`) — but a view-carrying return donates even there:
        // the view's referent is refcounted storage, not a raw buffer
        // core accounts for by hand.
        let core_frame = self.program_builder.programs[self.program].module
            == crate::compiling::module::ModuleId::Core;
        self.in_return_consume = true;
        match self.return_ty.clone() {
            Some(ret)
                if !self.returns_borrow
                    && (!core_frame || contains_borrow_classified(self.program_builder, &ret)) =>
            {
                if let Err(error) = self.consume_into(value, &ret, Span::SYNTHESIZED) {
                    self.deferred_errors.push(error);
                }
            }
            _ => {
                self.consume_operand(value);
            }
        }
        self.in_return_consume = false;
        if !self.writeback_params.is_empty() {
            let mut args = vec![value];
            args.extend(
                self.writeback_params
                    .iter()
                    .map(|local| Operand::Local(*local)),
            );
            let paired = self.fresh_local();
            self.push(Inst::Tuple { dest: paired, args });
            self.terminate(Term::Return(Operand::Local(paired)));
            return;
        }
        self.terminate(Term::Return(value));
    }

    fn emit_discontinue(&mut self, delimiter: Operand, value: Operand) {
        self.consume_operand(value);
        // Keep the abort in its own block. The release planner places this
        // clause frame's cleanup on the edge into it before the runtime
        // discontinues the suspended handled extent.
        let abort = self.new_block();
        self.terminate(Term::Goto(abort, Vec::new()));
        self.switch_to(abort);
        self.push(Inst::AbortTo {
            cont: delimiter,
            value,
        });
        self.terminate(Term::Trap("unreachable after discontinue"));
    }

    /// Emit scope-exit drops for every scope at depth >= `depth`, without
    /// popping them (the frames stay for the enclosing structure).
    /// Release a replaced value — or, while a live view roots at it,
    /// displace it to scope exit under a fresh anonymous binding so the
    /// view keeps reading the old value (snapshot semantics; the shape
    /// of Rust's temporary lifetime extension applied to reassignment).
    fn displace_or_drop(&mut self, local: LocalId, ty: &Ty) {
        if self.has_live_view(local) {
            let displaced = self.fresh_local();
            self.push(Inst::Copy {
                dest: displaced,
                src: Operand::Local(local),
            });
            self.record_flow(verify::FlowEvent::Move(local));
            self.own_local(displaced, ty);
            // The views now root at the displaced value: the owner's
            // next value starts with no views of its own.
            let views: Vec<LocalId> = self
                .borrow_roots
                .iter()
                .filter(|(_, root)| **root == local)
                .map(|(view, _)| *view)
                .collect();
            for view in views {
                self.borrow_roots.insert(view, displaced);
            }
            return;
        }
        self.record_flow(verify::FlowEvent::Drop(local));
        self.drop_value(Operand::Local(local), ty);
    }

    /// Structural teardown: RawPtr fields are refcounted buffers and free
    /// here; owned fields recurse; Borrowed views own nothing.
    fn drop_value(&mut self, value: Operand, ty: &Ty) {
        if matches!(ty, Ty::Borrow(_, _)) {
            return;
        }
        // Strict linearity (OWN-03): a linear value reaching an implicit
        // drop point was not consumed on this path — except a consuming
        // method's own receiver, whose drop IS the consumption.
        let sanctioned_param = matches!(value, Operand::Local(local) if local < self.param_floor)
            && !matches!(ty, Ty::Borrow(_, _));
        let consuming_own_receiver = self.consuming_receiver && matches!(value, Operand::Local(0));
        if is_linear(self.program_builder, ty)
            && !consuming_own_receiver
            && !sanctioned_param
            && !self.in_unwind_cleanup
        {
            self.deferred_errors.push(BackendError::new(
                format!(
                    "a linear `{}` value must be consumed exactly once on every path",
                    ty.render_mono()
                ),
                Span::SYNTHESIZED,
            ));
            return;
        }
        // Shared teardown: the type's structural drop is one synthesized
        // function per program, called here — except a shared drop
        // function's own root value, which must expand structurally
        // (nested occurrences of the same type are real recursion).
        if self.drop_glue_root.as_ref() == Some(ty) {
            self.drop_glue_root = None;
        } else if (contains_object(self.program_builder, ty)
            || needs_drop(self.program_builder, ty))
            && self.program_builder.drop_is_shared(ty)
        {
            match self.program_builder.value_glue(ty, Glue::Drop) {
                Ok(func) => {
                    let dest = self.fresh_local();
                    self.push(Inst::Call {
                        dest,
                        func,
                        args: vec![value],
                        unwind: None,
                    });
                }
                Err(error) => self.deferred_errors.push(error),
            }
            return;
        }
        // Region claims release first: one runtime scan covers any shape.
        // A `'heap` nominal's interior belongs to its region's teardown.
        if contains_object(self.program_builder, ty) {
            self.push(Inst::RegionRelease { src: value });
            if let Ty::Nominal(symbol, _) = ty
                && self
                    .program_builder
                    .struct_def(*symbol)
                    .is_some_and(|(def, _)| def.heap)
            {
                return;
            }
        }
        if !needs_drop(self.program_builder, ty) {
            return;
        }
        let mut ty = ty.clone();
        while let Ty::Borrow(_, inner) = ty {
            ty = *inner;
        }
        let ty = ty;
        match &ty {
            Ty::Any { .. } => {
                // The payload's teardown is behind the fixed drop slot.
                let witness = self.fresh_local();
                self.push(Inst::ExistentialWitness {
                    dest: witness,
                    src: value,
                    index: 0,
                });
                let payload = self.fresh_local();
                self.push(Inst::ExistentialPayload {
                    dest: payload,
                    src: value,
                });
                let dest = self.fresh_local();
                self.push(Inst::CallIndirect {
                    dest,
                    callee: Operand::Local(witness),
                    args: vec![Operand::Local(payload)],
                    unwind: None,
                });
            }
            Ty::Param(symbol) => {
                // A rigid effect-generic holds a native value; its
                // teardown dispatches through the frame's drop witness
                // (value-witness-table passing).
                if let Some((drop_witness, _)) =
                    self.param_witnesses.get(&self.canon_rigid(*symbol)).copied()
                {
                    let dest = self.fresh_local();
                    self.push(Inst::CallIndirect {
                        dest,
                        callee: Operand::Local(drop_witness),
                        args: vec![value],
                        unwind: None,
                    });
                } else {
                    self.deferred_errors.push(BackendError::unsupported(
                        format!(
                            "a generic value ({symbol:?}) cannot be released here without its ownership witnesses (not supported yet; in {} subst {:?})", self.flow_label,
                            self.subst
                        ),
                        Span::SYNTHESIZED,
                    ));
                }
            }
            Ty::Nominal(symbol, args) => {
                if let Some(payloads) = self.program_builder.variant_payloads(*symbol, args) {
                    self.drop_enum_value(value, payloads);
                    return;
                }
                // A `Deinit` conformance is the user's destructor hook: the
                // body runs first, then the glue tears fields down
                // structurally (the body never owns field teardown).
                if let Some((witness, subst)) = self.program_builder.deinit_witness(*symbol, args)
                    && let Ok(func) = self
                        .program_builder
                        .demand(witness, subst, Span::SYNTHESIZED)
                {
                    // Cleanup calls never nest their own unwind cleanup
                    // (drops cannot expose effects, CHG-08).
                    let mut call_args = vec![value];
                    match self.append_witness_args(func, &mut call_args, Span::SYNTHESIZED) {
                        Ok(()) => {
                            let dest = self.fresh_local();
                            self.push(Inst::Call {
                                dest,
                                func,
                                args: call_args,
                                unwind: None,
                            });
                        }
                        Err(error) => self.deferred_errors.push(error),
                    }
                }
                let Some(fields) = self.program_builder.field_types(*symbol, args) else {
                    return;
                };
                for (index, field_ty) in fields.iter().enumerate().rev() {
                    // Stored slots own: a borrow-typed field releases
                    // its referent (owning stored views).
                    let field_ty = &strip_borrows(field_ty.clone());
                    let field_is_ptr =
                        matches!(field_ty, Ty::Nominal(head, _) if *head == Symbol::RawPtr);
                    if field_is_ptr {
                        let field = self.fresh_local();
                        self.push(Inst::GetField {
                            dest: field,
                            src: value,
                            index: u16::try_from(index).unwrap_or_default(),
                        });
                        self.push(Inst::Free {
                            src: Operand::Local(field),
                        });
                        continue;
                    }
                    if !needs_drop(self.program_builder, field_ty) {
                        continue;
                    }
                    let field = self.fresh_local();
                    self.push(Inst::GetField {
                        dest: field,
                        src: value,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    self.drop_value(Operand::Local(field), field_ty);
                }
            }
            Ty::Tuple(items) => {
                for (index, item_ty) in items.iter().enumerate().rev() {
                    let item_ty = &strip_borrows(item_ty.clone());
                    if !needs_drop(self.program_builder, item_ty) {
                        continue;
                    }
                    let item = self.fresh_local();
                    self.push(Inst::TupleGet {
                        dest: item,
                        src: value,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    self.drop_value(Operand::Local(item), item_ty);
                }
            }
            Ty::Record(row) => {
                for (index, (_, item_ty)) in row.fields.iter().enumerate().rev() {
                    let item_ty = &strip_borrows(item_ty.clone());
                    if !needs_drop(self.program_builder, item_ty) {
                        continue;
                    }
                    let item = self.fresh_local();
                    self.push(Inst::TupleGet {
                        dest: item,
                        src: value,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    self.drop_value(Operand::Local(item), item_ty);
                }
            }
            _ => {}
        }
    }

    /// Enum payload drops dispatch on the tag: one arm per variant with
    /// owned payloads, joining back after.
    fn drop_enum_value(&mut self, value: Operand, payloads: Vec<Vec<Ty>>) {
        // Stored views own: a borrow-typed payload releases its referent
        // like any other stored reference.
        let payloads: Vec<Vec<Ty>> = payloads
            .into_iter()
            .map(|tys| tys.into_iter().map(strip_borrows).collect())
            .collect();
        let any_droppable = payloads.iter().any(|payload_tys| {
            payload_tys
                .iter()
                .any(|payload| needs_drop(self.program_builder, payload))
        });
        if !any_droppable {
            return;
        }
        let join = self.new_block();
        let tag = self.fresh_local();
        self.push(Inst::GetTag {
            dest: tag,
            src: value,
        });
        for (variant_tag, payload_tys) in payloads.iter().enumerate() {
            let droppable: Vec<(usize, &Ty)> = payload_tys
                .iter()
                .enumerate()
                .filter(|(_, payload)| needs_drop(self.program_builder, payload))
                .collect();
            if droppable.is_empty() {
                continue;
            }
            let arm = self.new_block();
            let next = self.new_block();
            self.branch_if_equal(
                ScalarOp::IntCmp(CmpKind::Eq),
                Operand::Local(tag),
                Operand::Const(Constant::Int(
                    i64::try_from(variant_tag).unwrap_or_default(),
                )),
                arm,
                next,
            );
            self.switch_to(arm);
            for (index, payload_ty) in droppable.iter().rev() {
                let payload = self.fresh_local();
                self.push(Inst::GetPayload {
                    dest: payload,
                    src: value,
                    index: u16::try_from(*index).unwrap_or_default(),
                });
                self.drop_value(Operand::Local(payload), payload_ty);
            }
            self.terminate(Term::Goto(join, Vec::new()));
            self.switch_to(next);
        }
        self.terminate(Term::Goto(join, Vec::new()));
        self.switch_to(join);
    }

    /// Enum payload retains dispatch on the tag: one arm per variant with
    /// buffer-carrying payloads, joining back after (`drop_enum_value`'s
    /// mirror for CheapClone).
    fn retain_enum_value(
        &mut self,
        value: Operand,
        payloads: Vec<Vec<Ty>>,
        span: Span,
    ) -> Result<(), BackendError> {
        let payloads: Vec<Vec<Ty>> = payloads
            .into_iter()
            .map(|tys| tys.into_iter().map(strip_borrows).collect())
            .collect();
        let any_retained = payloads.iter().any(|payload_tys| {
            payload_tys
                .iter()
                .any(|payload| donates(self.program_builder, payload))
        });
        if !any_retained {
            return Ok(());
        }
        let join = self.new_block();
        let tag = self.fresh_local();
        self.push(Inst::GetTag {
            dest: tag,
            src: value,
        });
        for (variant_tag, payload_tys) in payloads.iter().enumerate() {
            let retained: Vec<(usize, &Ty)> = payload_tys
                .iter()
                .enumerate()
                .filter(|(_, payload)| donates(self.program_builder, payload))
                .collect();
            if retained.is_empty() {
                continue;
            }
            let arm = self.new_block();
            let next = self.new_block();
            self.branch_if_equal(
                ScalarOp::IntCmp(CmpKind::Eq),
                Operand::Local(tag),
                Operand::Const(Constant::Int(
                    i64::try_from(variant_tag).unwrap_or_default(),
                )),
                arm,
                next,
            );
            self.switch_to(arm);
            for (index, payload_ty) in retained.iter() {
                let payload = self.fresh_local();
                self.push(Inst::GetPayload {
                    dest: payload,
                    src: value,
                    index: u16::try_from(*index).unwrap_or_default(),
                });
                self.retain_value(Operand::Local(payload), payload_ty, span)?;
            }
            self.terminate(Term::Goto(join, Vec::new()));
            self.switch_to(next);
        }
        self.terminate(Term::Goto(join, Vec::new()));
        self.switch_to(join);
        Ok(())
    }

    /// A consumer takes ownership of an operand: temps stop being
    /// statement-scoped, owned locals become moved. `'heap` handles have
    /// reference semantics — consuming a bound handle copies it and takes
    /// a fresh region claim instead of moving.
    /// The frame local a view ultimately derives from.
    fn borrow_root(&self, local: LocalId) -> LocalId {
        let mut current = local;
        let mut hops = 0;
        while let Some(next) = self.borrow_roots.get(&current) {
            if *next == current || hops > 64 {
                break;
            }
            current = *next;
            hops += 1;
        }
        current
    }

    /// Record a view's owner (call results with borrowed types).
    fn record_view(&mut self, result: Operand, source: Operand) {
        if let (Operand::Local(result), Operand::Local(source)) = (result, source) {
            let root = self.borrow_root(source);
            self.borrow_roots.insert(result, root);
        }
    }

    /// Propagate provenance only when the source already carries some
    /// (containers wrapping views, binds of views).
    fn propagate_view(&mut self, result: Operand, source: Operand) {
        if let (Operand::Local(_), Operand::Local(from)) = (result, source)
            && self.borrow_roots.contains_key(&from)
        {
            self.record_view(result, source);
        }
    }

    /// A loan is live while its view still has uses ahead.
    /// Whether a live view (a `Borrowed`-classified value whose symbol
    /// still has uses) roots at this local. Consuming or reassigning
    /// such an owner must keep the referent alive — snapshot semantics
    /// (docs/ownership-rethink-plan.md, rule 2's frame-local half).
    fn has_live_view(&self, root: LocalId) -> bool {
        self.borrow_roots.iter().any(|(view, candidate_root)| {
            *candidate_root == root
                && self.view_locals.contains(view)
                && !self.invalidated_views.contains(view)
                && self
                    .locals
                    .iter()
                    .find(|(_, local)| *local == view)
                    .is_some_and(|(symbol, _)| {
                        self.use_counts.get(symbol).copied().unwrap_or(0) > 0
                    })
        })
    }

    fn live_loan_of(&self, root: LocalId, exclusive_only: bool) -> Option<&Loan> {
        self.loans.iter().find(|loan| {
            loan.root == root
                && (!exclusive_only || loan.exclusive)
                && (self.use_counts.get(&loan.view_symbol).copied().unwrap_or(0) > 0
                    || self.loop_stack.len() > loan.loop_depth)
        })
    }

    /// Moving or reassigning an owner invalidates its live views —
    /// only genuinely view-typed locals; owned donations survive.
    fn invalidate_views_of(&mut self, owner: LocalId) {
        let views: Vec<LocalId> = self
            .borrow_roots
            .iter()
            .filter(|(view, root)| **root == owner && self.view_locals.contains(*view))
            .map(|(view, _)| *view)
            .collect();
        self.invalidated_views.extend(views);
    }

    fn consume_operand(&mut self, operand: Operand) -> bool {
        let Operand::Local(local) = operand else {
            return true;
        };
        if let Some(position) = self.stmt_temps.iter().position(|temp| *temp == local) {
            // Consuming a temp removes it from this path's live list
            // only. owned_tys is a type table shared across sibling
            // control-flow arms (merge restores moved/stmt_temps per
            // arm, never owned_tys): deleting from it here made a
            // sibling arm's exit flush skip its own copy's drop — a
            // real leak, caught by the balance verifier.
            self.stmt_temps.remove(position);
            self.record_flow(verify::FlowEvent::Move(local));
            return true;
        }
        if let Some(ty) = self.owned_tys.get(&local).cloned() {
            if !needs_drop(self.program_builder, &ty) && contains_object(self.program_builder, &ty)
            {
                self.push(Inst::RegionAcquire { src: operand });
                return true;
            }
            // Rule 1 (docs/ownership-rethink-plan.md): a consume that
            // is not the value's last use donates a reference instead
            // of moving — ownership is an optimization the compiler
            // discovers at the true last use (Perceus: Reinking, Xie,
            // de Moura & Leijen, PLDI 2021), never a proof burden.
            // Inside a loop the binding's uses recur, so an outer
            // binding always shares. Linear and unique values keep move
            // semantics: duplicating one is what those markers exist to
            // prevent.
            if !is_linear(self.program_builder, &ty)
                && !self.unique_locals.contains(&local)
                && !self.in_return_consume
                && self.can_release(&ty)
            {
                let remaining = self
                    .locals
                    .iter()
                    .find(|(_, candidate)| **candidate == local)
                    .and_then(|(symbol, _)| self.use_counts.get(symbol))
                    .copied()
                    .unwrap_or(0);
                let bound_outside_loop = self
                    .owned_loop_depth
                    .get(&local)
                    .is_some_and(|depth| self.loop_stack.len() > *depth);
                if remaining > 0 || bound_outside_loop || self.has_live_view(local) {
                    if let Err(error) = self.retain_value(operand, &ty, Span::SYNTHESIZED) {
                        self.deferred_errors.push(error);
                    }
                    self.record_flow(verify::FlowEvent::Use(local));
                    return true;
                }
            }
            // Only a live `&mut` loan blocks the move: shared loans
            // snapshot (the adjudicated exclusivity rule — conflicts
            // require the in-place-write contract aliasing would break).
            if let Some(loan) = self.live_loan_of(local, true) {
                self.deferred_errors.push(BackendError::new(
                    format!(
                        "cannot move a value while it is borrowed as `{}`",
                        loan.view_name
                    ),
                    Span::SYNTHESIZED,
                ));
                // The loan conflict is the error; keep the view usable
                // so this diagnostic surfaces instead of a downstream
                // use-of-borrowed error.
                self.moved.insert(local);
                self.record_flow(verify::FlowEvent::Move(local));
                return true;
            }
            self.moved.insert(local);
            self.record_flow(verify::FlowEvent::Move(local));
            self.invalidate_views_of(local);
            return true;
        }
        // Consuming a global donates a reference (the runtime is
        // balanced either way); under implicit sharing later uses share
        // too, so only linear globals keep move discipline — exactly
        // once, never duplicated.
        if let Some(slot) = self.global_loads.get(&local).copied() {
            let global_ty = self
                .program_builder
                .global_tys
                .get(&slot)
                .cloned()
                .unwrap_or(Ty::Error);
            if is_linear(self.program_builder, &global_ty) && !self.moved_globals.insert(slot) {
                self.deferred_errors.push(BackendError::new(
                    "use of moved value: this global was already consumed".into(),
                    Span::SYNTHESIZED,
                ));
            }
        }
        false
    }

    /// Transfer an operand into a binding or store destination. A
    /// borrow-typed (or `Borrowed`-view) destination takes no ownership:
    /// the operand is consumed as a temporary but never retained.
    fn consume_binding(
        &mut self,
        operand: Operand,
        ty: &Ty,
        span: Span,
    ) -> Result<(), BackendError> {
        // A bare borrow-typed destination is a loan — an inferred-
        // borrow `let` takes no ownership (frames borrow). Stored
        // slots own: construction sites strip their slot types before
        // calling here, so a borrow-typed field donates its inner
        // reference, and marked view nominals consume like any struct
        // (owning stored views).
        let resolved = self.resolved(ty);
        if matches!(resolved, Ty::Borrow(_, _)) {
            if let Operand::Local(local) = operand
                && let Some(position) = self.stmt_temps.iter().position(|temp| *temp == local)
            {
                self.stmt_temps.remove(position);
                if self.owned_tys.contains_key(&local) {
                    self.record_flow(verify::FlowEvent::Move(local));
                }
            }
            return Ok(());
        }
        self.consume_into(operand, &resolved, span)
    }

    /// Transfer an operand into an owning position. A place read that
    /// cannot move (a field projection, a global) donates a fresh
    /// reference instead: both owners hold the buffers (the deleted flow
    /// checker's clone-coercion rule, now MIR's).
    fn consume_into(&mut self, operand: Operand, ty: &Ty, span: Span) -> Result<(), BackendError> {
        if !self.consume_operand(operand) {
            let mut owned = self.resolved(ty);
            while let Ty::Borrow(_, inner) = owned {
                owned = *inner;
            }
            // A bare RawPtr is a manually managed scalar (core's own
            // buffer code); only structured owners donate references.
            let bare_pointer =
                matches!(&owned, Ty::Nominal(symbol, _) if *symbol == Symbol::RawPtr);
            if !bare_pointer && donates(self.program_builder, &owned) {
                // Taking an owned value out of a shared borrow donates a
                // reference like any other place read: under implicit
                // sharing every clone at this boundary is a retain, so
                // the old Copy/CheapClone cheapness gate has nothing
                // left to police (docs/ownership-rethink-plan.md,
                // cheap-clone-at-use adjudication).
                self.retain_value(operand, &owned, span)?;
            }
        }
        Ok(())
    }

    /// Whether this frame can release a value of `ty` later: every bare
    /// generic in it needs a drop witness. A witness-less frame (an
    /// uninstantiated body compiled for checking only) keeps move
    /// semantics — sharing there would strand the value at scope exit.
    fn can_release(&self, ty: &Ty) -> bool {
        witness_params(std::slice::from_ref(&(Symbol::RawPtr, ty.clone())))
            .iter()
            .all(|symbol| self.param_witnesses.contains_key(&self.canon_rigid(*symbol)))
    }

    /// Owned parts to drop OR region claims to release OR linear values to
    /// account for: either way the binding gets scope-exit processing.
    fn needs_release(&self, ty: &Ty) -> bool {
        needs_drop(self.program_builder, ty)
            || (!matches!(ty, Ty::Borrow(_, _))
                && (contains_object(self.program_builder, ty)
                    || is_linear(self.program_builder, ty)))
    }

    /// Register an owned rvalue temporary for the current statement.
    fn produce_temp(&mut self, local: LocalId, ty: &Ty) {
        if self.needs_release(ty) {
            self.owned_tys.insert(local, ty.clone());
            self.owned_loop_depth.insert(local, self.loop_stack.len());
            self.stmt_temps.push(local);
            self.record_flow(verify::FlowEvent::Def(local));
        }
    }

    /// Register a binding as a scope-owned droppable local.
    fn own_local(&mut self, local: LocalId, ty: &Ty) {
        if self.needs_release(ty) {
            self.owned_tys.insert(local, ty.clone());
            self.owned_loop_depth.insert(local, self.loop_stack.len());
            if let Some(scope) = self.scopes.last_mut() {
                scope.push(local);
            }
            self.record_flow(verify::FlowEvent::Def(local));
        }
    }

    /// Merge compiled control-flow arms at a join (Ryu-style structural
    /// path-sensitive cleanup): a local moved on some paths drops at the
    /// end of every path that still owns it, and reads after the join
    /// reject as moved.
    fn merge_arms(
        &mut self,
        arms: Vec<ArmEnd>,
        result: LocalId,
        join: BlockId,
        temps_before: Vec<LocalId>,
        moved_before: rustc_hash::FxHashSet<LocalId>,
    ) {
        // First pass: each arm consumes its value into the result. The
        // consumption itself can move a local (an arm whose value IS a
        // binding), so the union is computed after it.
        let mut states: Vec<(
            BlockId,
            Operand,
            rustc_hash::FxHashSet<LocalId>,
            Vec<LocalId>,
        )> = Vec::new();
        let mut globals_union: rustc_hash::FxHashSet<u32> = rustc_hash::FxHashSet::default();
        for arm in arms {
            self.switch_to(arm.block);
            self.moved = arm.moved;
            globals_union.extend(arm.moved_globals.iter().copied());
            self.stmt_temps = arm.temps;
            self.consume_operand(arm.value);
            // The join value inherits any arm's borrow provenance.
            self.propagate_view(Operand::Local(result), arm.value);
            states.push((
                arm.block,
                arm.value,
                std::mem::take(&mut self.moved),
                std::mem::take(&mut self.stmt_temps),
            ));
        }
        // The union runs over the arm end-states only: each arm started
        // from the pre-branch state, so a value moved before the branch
        // is still in every arm that did not restore it — and a value
        // reassigned on every path comes back clean.
        let mut union: rustc_hash::FxHashSet<LocalId> = rustc_hash::FxHashSet::default();
        for (_, _, moved, _) in &states {
            union.extend(moved.iter().copied());
        }
        if states.is_empty() {
            union = moved_before.clone();
        }
        // Only locals that exist OUTSIDE the arms can diverge: an
        // arm-declared binding lives and dies inside its own scope.
        // Second pass: a local another path moved drops at the end of
        // every path that still owns it; nothing after the join may use it
        // (path-sensitive structural cleanup).
        for (block, value, moved, temps) in states {
            self.switch_to(block);
            self.moved = moved;
            self.stmt_temps = temps;
            self.stmt_temps.truncate(temps_before.len());
            self.terminate(Term::Goto(join, vec![value]));
        }
        self.blocks[join].params.push(result);
        self.moved = union;
        // A global moved on any path stays moved after the join (a
        // reassignment on every path clears it on every path).
        self.moved_globals = globals_union;
        self.stmt_temps = temps_before;
        self.switch_to(join);
    }

    /// Drop the current statement's unconsumed temporaries (latest first).
    fn flush_stmt_temps(&mut self, keep: Option<Operand>) {
        self.flush_stmt_temps_above(0, keep);
    }

    /// Drop the statement temporaries above `floor`, leaving temps that
    /// belong to enclosing statements (a match arm's owned bindings, an
    /// outer statement's operands) to their own boundaries.
    fn flush_stmt_temps_above(&mut self, floor: usize, keep: Option<Operand>) {
        let keep = match keep {
            Some(Operand::Local(local)) => Some(local),
            _ => None,
        };
        let mut kept_was_temp = false;
        while self.stmt_temps.len() > floor {
            let Some(temp) = self.stmt_temps.pop() else {
                break;
            };
            if Some(temp) == keep {
                kept_was_temp = true;
                continue;
            }
        }
        // A kept TEMP survives to the enclosing statement's boundary. A
        // kept scope binding is not a temp: its scope still owns it.
        if kept_was_temp && let Some(kept) = keep {
            self.stmt_temps.push(kept);
        }
    }

    fn fresh_local(&mut self) -> LocalId {
        let local = self.next_local;
        self.next_local += 1;
        local
    }

    fn new_block(&mut self) -> BlockId {
        self.blocks.push(BlockData::default());
        self.blocks.len() - 1
    }

    fn switch_to(&mut self, block: BlockId) {
        self.current = block;
    }

    fn terminated(&self) -> bool {
        self.blocks[self.current].term.is_some()
    }

    fn push(&mut self, inst: Inst) {
        if !self.terminated() {
            self.blocks[self.current].insts.push(inst);
        }
    }

    fn terminate(&mut self, term: Term) {
        if !self.terminated() {
            self.blocks[self.current].term = Some(term);
        }
    }

    /// Emit a direct call; the release planner fills its abort-unwind
    /// entry after the function is built.
    fn push_call(&mut self, dest: LocalId, func: FuncId, args: Vec<Operand>) {
        self.push(Inst::Call {
            dest,
            func,
            args,
            unwind: None,
        });
    }

    /// Resolve a projection spine (`o.inner.v`) down to its base binding.
    /// Links run base-outward; each records its field index, whether the
    /// parent is a `'heap` object, and the field's type.
    fn resolve_place(&mut self, expr: &Expr) -> Result<Option<PlaceChain>, BackendError> {
        match &expr.kind {
            ExprKind::Variable(Name::Resolved(symbol, _)) => {
                if let Some(local) = self.locals.get(symbol).copied() {
                    return Ok(Some(PlaceChain {
                        base: local,
                        global_slot: None,
                        links: Vec::new(),
                    }));
                }
                if let Some(slot) = self.program_builder.global_slots.get(symbol).copied() {
                    let base = self.fresh_local();
                    self.push(Inst::GlobalLoad {
                        dest: base,
                        global: slot,
                    });
                    return Ok(Some(PlaceChain {
                        base,
                        global_slot: Some(slot),
                        links: Vec::new(),
                    }));
                }
                Ok(None)
            }
            ExprKind::Member(base_expr, crate::label::Label::Named(name)) => {
                let Some(base) = base_expr else {
                    return Ok(None);
                };
                let mut head = self.resolved(&base.ty);
                while let Ty::Borrow(_, inner) = head {
                    head = *inner;
                }
                let Ty::Record(row) = head else {
                    return Ok(None);
                };
                let Some(mut chain) = self.resolve_place(base)? else {
                    return Ok(None);
                };
                let Some(index) = row.fields.iter().position(|(label, _)| {
                    matches!(label, crate::label::Label::Named(field) if field == name)
                }) else {
                    return Ok(None);
                };
                let field_ty = row.fields[index].1.clone();
                chain.links.push(PlaceLink {
                    index: u16::try_from(index).unwrap_or_default(),
                    heap: false,
                    field_ty,
                    record_arity: Some(u16::try_from(row.fields.len()).unwrap_or_default()),
                });
                Ok(Some(chain))
            }
            ExprKind::Proj(base, _, field) => {
                let Some(mut chain) = self.resolve_place(base)? else {
                    return Ok(None);
                };
                let module = self.program_builder.programs[self.program].module;
                let base_ty = self.resolved(&base.ty);
                let mut head = &base_ty;
                while let Ty::Borrow(_, inner) = head {
                    head = inner;
                }
                let Ty::Nominal(struct_symbol, _) = head else {
                    return Ok(None);
                };
                let struct_symbol = canonical(*struct_symbol, module);
                let field = canonical(*field, module);
                let Some(index) = self.program_builder.field_index(struct_symbol, field) else {
                    return Ok(None);
                };
                let heap = self
                    .program_builder
                    .struct_def(struct_symbol)
                    .is_some_and(|(def, _)| def.heap);
                let field_ty = self
                    .program_builder
                    .field_types(struct_symbol, head_args(head))
                    .and_then(|fields| fields.get(usize::from(index)).cloned())
                    .unwrap_or(Ty::Error);
                chain.links.push(PlaceLink {
                    index,
                    heap,
                    field_ty,
                    record_arity: None,
                });
                Ok(Some(chain))
            }
            _ => Ok(None),
        }
    }

    /// Store `value` into a resolved place, dropping the displaced leaf
    /// value (unless `in_init`). Records are copy-on-write, so each value
    /// link writes back into its parent, stopping at the first `'heap`
    /// link (objects mutate in place); a chain of value links writes back
    /// into the base local or global slot.
    fn write_place(
        &mut self,
        chain: &PlaceChain,
        value: Operand,
        value_ty: &Ty,
        span: Span,
        assign: bool,
    ) -> Result<(), BackendError> {
        if chain.links.is_empty() {
            if let Some(slot) = chain.global_slot {
                if assign && self.needs_release(value_ty) {
                    let old = self.fresh_local();
                    self.push(Inst::GlobalLoad {
                        dest: old,
                        global: slot,
                    });
                    self.drop_value(Operand::Local(old), value_ty);
                }
                if assign {
                    // Global slots own: a borrow-typed value donates
                    // its inner reference on the way in.
                    self.consume_binding(value, &strip_borrows(value_ty.clone()), span)?;
                }
                self.push(Inst::GlobalStore {
                    global: slot,
                    src: value,
                });
            } else {
                if assign {
                    if let Some(ty) = self.owned_tys.get(&chain.base).cloned() {
                        if !self.moved.contains(&chain.base) {
                            self.displace_or_drop(chain.base, &ty);
                        }
                        self.moved.remove(&chain.base);
                    }
                    self.consume_binding(value, value_ty, span)?;
                }
                self.push(Inst::Copy {
                    dest: chain.base,
                    src: value,
                });
                if assign && self.owned_tys.contains_key(&chain.base) {
                    self.record_flow(verify::FlowEvent::Def(chain.base));
                }
            }
            return Ok(());
        }
        // Descend to the leaf's parent, keeping each value-link parent for
        // the write-back pass.
        let mut current = chain.base;
        let mut parents: Vec<(LocalId, PlaceLink)> = Vec::new();
        for link in &chain.links[..chain.links.len() - 1] {
            let child = self.fresh_local();
            if link.heap {
                self.push(Inst::ObjectGet {
                    dest: child,
                    src: Operand::Local(current),
                    index: link.index,
                });
            } else {
                self.push(Inst::GetField {
                    dest: child,
                    src: Operand::Local(current),
                    index: link.index,
                });
            }
            parents.push((current, link.clone()));
            current = child;
        }
        let leaf = &chain.links[chain.links.len() - 1];
        if leaf.heap {
            // Region containment replaces the stored claim; the old
            // field's interior belongs to the region graph.
            if assign {
                // Stored slots own (owning stored views).
                self.consume_binding(value, &strip_borrows(leaf.field_ty.clone()), span)?;
            }
            self.push(Inst::ObjectSet {
                obj: Operand::Local(current),
                src: value,
                index: leaf.index,
            });
            if assign && contains_object(self.program_builder, value_ty) {
                self.push(Inst::RegionRelease { src: value });
            }
        } else {
            if assign && !self.in_init && needs_drop(self.program_builder, &leaf.field_ty) {
                let old = self.fresh_local();
                self.push(Inst::GetField {
                    dest: old,
                    src: Operand::Local(current),
                    index: leaf.index,
                });
                let field_ty = leaf.field_ty.clone();
                self.drop_value(Operand::Local(old), &field_ty);
            }
            if assign {
                // Stored slots own (owning stored views).
                self.consume_binding(value, &strip_borrows(leaf.field_ty.clone()), span)?;
            }
            if let Some(arity) = leaf.record_arity {
                let rebuilt = self.rebuild_tuple(current, leaf.index, value, arity);
                self.push(Inst::Copy {
                    dest: current,
                    src: Operand::Local(rebuilt),
                });
            } else {
                self.push(Inst::SetField {
                    rec: current,
                    src: value,
                    index: leaf.index,
                });
            }
        }
        // Write updated records back up through the value links; a `'heap`
        // parent absorbs the mutation in place.
        let mut updated = current;
        for (parent, link) in parents.into_iter().rev() {
            if link.heap {
                self.push(Inst::ObjectSet {
                    obj: Operand::Local(parent),
                    src: Operand::Local(updated),
                    index: link.index,
                });
                return Ok(());
            }
            if let Some(arity) = link.record_arity {
                let rebuilt =
                    self.rebuild_tuple(parent, link.index, Operand::Local(updated), arity);
                self.push(Inst::Copy {
                    dest: parent,
                    src: Operand::Local(rebuilt),
                });
            } else {
                self.push(Inst::SetField {
                    rec: parent,
                    src: Operand::Local(updated),
                    index: link.index,
                });
            }
            updated = parent;
        }
        if chain.links.first().is_some_and(|link| link.heap) {
            return Ok(());
        }
        if let Some(slot) = chain.global_slot {
            self.push(Inst::GlobalStore {
                global: slot,
                src: Operand::Local(updated),
            });
        }
        Ok(())
    }

    /// A literal String value (immortal static bytes behind the core
    /// String layout).
    fn emit_string_lit(&mut self, text: &str) -> Operand {
        let dest = self.fresh_local();
        self.push(Inst::StringLit {
            dest,
            bytes: text.as_bytes().to_vec(),
        });
        Operand::Local(dest)
    }

    /// `left + right` through the `String: Add` witness, dropping both
    /// inputs (String frees no-op on static storage).
    fn emit_string_concat(
        &mut self,
        left: Operand,
        right: Operand,
        span: Span,
    ) -> Result<Operand, BackendError> {
        let string_ty = Ty::Nominal(Symbol::String, Vec::new());
        let add = self.program_builder.protocol_named("Add").ok_or_else(|| {
            BackendError::new("derived show without the Add protocol".into(), span)
        })?;
        let add_ref = crate::types::ty::ProtocolRef {
            protocol: add,
            args: vec![string_ty.clone()],
        };
        let label = crate::label::Label::Named("add".into());
        let (implementation, subst) = self
            .program_builder
            .conformance_witness(&string_ty, &add_ref, &label)
            .or_else(|| {
                let bare = crate::types::ty::ProtocolRef {
                    protocol: add,
                    args: Vec::new(),
                };
                self.program_builder
                    .conformance_witness(&string_ty, &bare, &label)
            })
            .ok_or_else(|| {
                BackendError::new(
                    "derived show without a String concatenation witness".into(),
                    span,
                )
            })?;
        let func = self.program_builder.demand(implementation, subst, span)?;
        self.program_builder
            .writeback_expectations
            .push((func, 0, span));
        let dest = self.fresh_local();
        self.push(Inst::Call {
            dest,
            func,
            args: vec![left, right],
            unwind: None,
        });
        self.drop_value(left, &string_ty);
        self.drop_value(right, &string_ty);
        Ok(Operand::Local(dest))
    }

    /// Render one value: its real `show` conformance when one exists,
    /// else the derived chunk for its structure.
    fn emit_sub_show(
        &mut self,
        value: Operand,
        ty: &Ty,
        protocol: &crate::types::ty::ProtocolRef,
        span: Span,
    ) -> Result<Operand, BackendError> {
        let mut ty = ty.clone();
        while let Ty::Borrow(_, inner) = ty {
            ty = *inner;
        }
        let label = crate::label::Label::Named("show".into());
        let func = match self
            .program_builder
            .conformance_witness(&ty, protocol, &label)
        {
            Some((implementation, subst)) => {
                self.program_builder.demand(implementation, subst, span)?
            }
            None => self.program_builder.derived_show(&ty, protocol, span)?,
        };
        self.program_builder
            .writeback_expectations
            .push((func, 0, span));
        let dest = self.fresh_local();
        self.push(Inst::Call {
            dest,
            func,
            args: vec![value],
            unwind: None,
        });
        Ok(Operand::Local(dest))
    }

    /// Structural equality of two operands of one type: real conformances
    /// at nominal leaves, tag dispatch plus payload-wise recursion for
    /// enums, field-wise recursion for structs, element-wise for tuples
    /// and records. Short-circuits to false at the first mismatch.
    fn emit_equality(
        &mut self,
        a: Operand,
        b: Operand,
        ty: &Ty,
        protocol: &crate::types::ty::ProtocolRef,
        span: Span,
    ) -> Result<Operand, BackendError> {
        let mut ty = ty.clone();
        while let Ty::Borrow(_, inner) = ty {
            ty = *inner;
        }
        // Each recursion level compares values of a NEW type, so the
        // protocol application is rebuilt for it (`Equatable<RHS = Self>`);
        // the caller's application describes the outer type only.
        let target = self
            .program_builder
            .catalog
            .derived_protocol_ref(protocol.protocol, &ty)
            .unwrap_or_else(|| crate::types::ty::ProtocolRef::bare(protocol.protocol));
        let protocol = &target;
        match &ty {
            Ty::Nominal(symbol, args) => {
                let label = crate::label::Label::Named("equals".into());
                if let Some((implementation, subst)) = self
                    .program_builder
                    .conformance_witness(&ty, protocol, &label)
                {
                    let func = self.program_builder.demand(implementation, subst, span)?;
                    self.program_builder
                        .writeback_expectations
                        .push((func, 0, span));
                    let dest = self.fresh_local();
                    self.push(Inst::Call {
                        dest,
                        func,
                        args: vec![a, b],
                        unwind: None,
                    });
                    return Ok(Operand::Local(dest));
                }
                if let Some(payloads) = self.program_builder.variant_payloads(*symbol, args) {
                    return self.emit_enum_equality(a, b, payloads, protocol, span);
                }
                if let Some(fields) = self.program_builder.field_types(*symbol, args) {
                    let pairs: Vec<(u16, Ty)> = fields
                        .iter()
                        .enumerate()
                        .map(|(ix, field)| (u16::try_from(ix).unwrap_or_default(), field.clone()))
                        .collect();
                    return self.emit_field_equality(a, b, &pairs, false, protocol, span);
                }
                Err(BackendError::unsupported(
                    "derived equality on this type is not supported yet".into(),
                    span,
                ))
            }
            Ty::Tuple(items) => {
                let pairs: Vec<(u16, Ty)> = items
                    .iter()
                    .enumerate()
                    .map(|(ix, item)| (u16::try_from(ix).unwrap_or_default(), item.clone()))
                    .collect();
                self.emit_field_equality(a, b, &pairs, true, protocol, span)
            }
            Ty::Record(row) => {
                let pairs: Vec<(u16, Ty)> = row
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(ix, (_, item))| (u16::try_from(ix).unwrap_or_default(), item.clone()))
                    .collect();
                self.emit_field_equality(a, b, &pairs, true, protocol, span)
            }
            _ => Err(BackendError::unsupported(
                "derived equality on this type is not supported yet".into(),
                span,
            )),
        }
    }

    /// All-fields-equal with early exit; `tuple_layout` selects TupleGet
    /// over GetField.
    fn emit_field_equality(
        &mut self,
        a: Operand,
        b: Operand,
        fields: &[(u16, Ty)],
        tuple_layout: bool,
        protocol: &crate::types::ty::ProtocolRef,
        span: Span,
    ) -> Result<Operand, BackendError> {
        let result = self.fresh_local();
        let fail = self.new_block();
        let done = self.new_block();
        for (index, field_ty) in fields {
            let fa = self.fresh_local();
            let fb = self.fresh_local();
            if tuple_layout {
                self.push(Inst::TupleGet {
                    dest: fa,
                    src: a,
                    index: *index,
                });
                self.push(Inst::TupleGet {
                    dest: fb,
                    src: b,
                    index: *index,
                });
            } else {
                self.push(Inst::GetField {
                    dest: fa,
                    src: a,
                    index: *index,
                });
                self.push(Inst::GetField {
                    dest: fb,
                    src: b,
                    index: *index,
                });
            }
            let equal = self.emit_equality(
                Operand::Local(fa),
                Operand::Local(fb),
                field_ty,
                protocol,
                span,
            )?;
            let next = self.new_block();
            self.terminate(Term::Branch {
                cond: equal,
                then_block: next,
                else_block: fail,
            });
            self.switch_to(next);
        }
        self.push(Inst::Copy {
            dest: result,
            src: Operand::Const(Constant::Bool(true)),
        });
        self.terminate(Term::Goto(done, Vec::new()));
        self.switch_to(fail);
        self.push(Inst::Copy {
            dest: result,
            src: Operand::Const(Constant::Bool(false)),
        });
        self.terminate(Term::Goto(done, Vec::new()));
        self.switch_to(done);
        Ok(Operand::Local(result))
    }

    /// Compile a call's arguments, recording the destination place for
    /// each `mut` argument — the capture half of the writeback convention.
    fn compile_call_args(
        &mut self,
        args: &[crate::typed_ast::CallArg],
        operands: &mut Vec<Operand>,
        mut_arg_places: &mut Vec<(usize, PlaceChain)>,
    ) -> Result<(), BackendError> {
        for arg in args {
            let mut operand = self.compile_expr(&arg.value)?;
            if matches!(arg.mode, Some(ArgMode::Mut)) {
                let Some(chain) = self.resolve_place(&arg.value)? else {
                    return Err(BackendError::unsupported(
                        "a `mut` argument must name a mutable place".into(),
                        arg.value.span,
                    ));
                };
                mut_arg_places.push((operands.len(), chain));
            }
            // An explicit `copy` marker clones at the argument site: the
            // callee consumes the fresh copy and the source stays put.
            if matches!(arg.mode, Some(ArgMode::Copy)) {
                let mut ty = self.resolved(&arg.value.ty);
                while let Ty::Borrow(_, inner) = ty {
                    ty = *inner;
                }
                let canonical_ty =
                    canonical_ty(&ty, self.program_builder.programs[self.program].module);
                if self.needs_release(&ty)
                    && !conforms_to(self.program_builder, &canonical_ty, Symbol::CheapClone)
                {
                    return Err(BackendError::new(
                        "the `copy` marker requires a Copy or CheapClone value".into(),
                        arg.value.span,
                    ));
                }
                let dest = self.fresh_local();
                self.push(Inst::Copy { dest, src: operand });
                if donates(self.program_builder, &ty) {
                    self.retain_value(Operand::Local(dest), &ty, arg.value.span)?;
                }
                self.produce_temp(dest, &ty);
                operand = Operand::Local(dest);
            }
            operands.push(operand);
        }
        Ok(())
    }

    /// Collect one writeback target per exclusive-borrow parameter, the
    /// receiver's slot first when the callee is a `mut func` method —
    /// mirroring the callee's `writeback_params` order.
    fn writeback_targets(
        &mut self,
        callee_ty: &Ty,
        operand_count: usize,
        receiver: Option<Option<WritebackTarget>>,
        mut_arg_places: &[(usize, PlaceChain)],
        args: &[crate::typed_ast::CallArg],
        args_operand_offset: usize,
    ) -> Result<Vec<Option<WritebackTarget>>, BackendError> {
        let mut targets: Vec<Option<WritebackTarget>> = Vec::new();
        let has_receiver = receiver.is_some();
        if let Some(receiver) = receiver {
            targets.push(receiver);
        }
        if let Ty::Func(params, _, _) = callee_ty {
            let offset = operand_count.saturating_sub(params.len());
            for (ix, param) in params.iter().enumerate() {
                let position = offset + ix;
                if matches!(param, Ty::Borrow(Perm::Exclusive, _))
                    && !(has_receiver && position == 0)
                {
                    let mut place = mut_arg_places
                        .iter()
                        .find(|(operand_ix, _)| *operand_ix == position)
                        .map(|(_, chain)| chain.clone());
                    if place.is_none() {
                        // The checker passes a place to a `mut` parameter
                        // without requiring the call-site marker; the
                        // evolved value still writes back.
                        if let Some(arg) = position
                            .checked_sub(args_operand_offset)
                            .and_then(|arg_ix| args.get(arg_ix))
                        {
                            place = self.resolve_place(&arg.value)?;
                            if place.is_none() {
                                // An rvalue has no place: its evolution
                                // would be unobservable.
                                return Err(BackendError::new(
                                    "a `mut` parameter requires a mutable place argument".into(),
                                    arg.value.span,
                                ));
                            }
                        }
                    }
                    targets.push(place.map(WritebackTarget::Place));
                }
            }
        }
        Ok(targets)
    }

    /// The landing half of the `(result, final mut values…)` convention:
    /// with no targets the call's value IS the result; otherwise unpack
    /// the pair and store each evolved value back into its place.
    fn apply_writebacks(
        &mut self,
        dest: LocalId,
        targets: Vec<Option<WritebackTarget>>,
        result_ty: &Ty,
        span: Span,
    ) -> Result<Operand, BackendError> {
        if targets.is_empty() {
            self.produce_temp(dest, result_ty);
            return Ok(Operand::Local(dest));
        }
        let result = self.fresh_local();
        self.push(Inst::TupleGet {
            dest: result,
            src: Operand::Local(dest),
            index: 0,
        });
        for (position, target) in targets.into_iter().enumerate() {
            let Some(target) = target else {
                continue;
            };
            let updated = self.fresh_local();
            self.push(Inst::TupleGet {
                dest: updated,
                src: Operand::Local(dest),
                index: u16::try_from(position + 1).unwrap_or_default(),
            });
            match target {
                WritebackTarget::Place(chain) => {
                    self.write_place(&chain, Operand::Local(updated), &Ty::Error, span, false)?;
                }
                WritebackTarget::Repack {
                    chain,
                    protocol,
                    witnesses,
                } => {
                    // An existential's `mut` requirement evolves the
                    // payload, not the wrapper: rebuild around the evolved
                    // payload with the receiver's own witness table.
                    let packed = self.fresh_local();
                    self.push(Inst::ExistentialPack {
                        dest: packed,
                        protocol,
                        payload: Operand::Local(updated),
                        witnesses,
                    });
                    self.write_place(&chain, Operand::Local(packed), &Ty::Error, span, false)?;
                }
            }
        }
        self.produce_temp(result, result_ty);
        Ok(Operand::Local(result))
    }

    /// Whether a protocol requirement is declared `mut func`: its scheme's
    /// receiver parameter is an exclusive borrow, so every implementation
    /// returns `(result, final self)` for the caller's writeback.
    fn requirement_is_mut(&self, protocol: Symbol, name: &str) -> bool {
        let Some(requirement) = self.program_builder.requirement_symbol(protocol, name) else {
            return false;
        };
        self.program_builder.programs.iter().any(|input| {
            input
                .program
                .types()
                .schemes
                .iter()
                .any(|(symbol, scheme)| {
                    canonical(*symbol, input.module) == requirement
                        && matches!(
                            &scheme.ty,
                            Ty::Func(params, _, _)
                                if matches!(
                                    params.first(),
                                    Some(Ty::Borrow(Perm::Exclusive, _))
                                )
                        )
                })
        })
    }

    /// Rebuild a tuple-layout value with one slot replaced (runtime
    /// records are tuples; tuples are immutable, so writes copy).
    fn rebuild_tuple(
        &mut self,
        source: LocalId,
        replaced: u16,
        value: Operand,
        arity: u16,
    ) -> LocalId {
        let mut args = Vec::new();
        for index in 0..arity {
            if index == replaced {
                args.push(value);
                continue;
            }
            let item = self.fresh_local();
            self.push(Inst::TupleGet {
                dest: item,
                src: Operand::Local(source),
                index,
            });
            args.push(Operand::Local(item));
        }
        let dest = self.fresh_local();
        self.push(Inst::Tuple { dest, args });
        dest
    }

    /// The one spelling `param_witnesses`/`param_requirements` key by. A
    /// rigid reaches the frame in two spellings — the typed tree's
    /// module-local symbol and a substitution's imported one — so every
    /// insert and lookup normalizes through here (the map-key analog of
    /// `demand`'s dual-spelling subst filter).
    fn canon_rigid(&self, symbol: Symbol) -> Symbol {
        canonical(
            symbol,
            self.program_builder.programs[self.program].module,
        )
    }

    /// Bind the hidden argument block for each rigid generic at
    /// consecutive locals starting at `base`: `[drop, retain]`, then each
    /// constraint protocol's requirement closures in declaration order.
    /// Returns the first local past the block. Callers append arguments in
    /// exactly this layout.
    fn bind_witness_params(&mut self, params: &[Symbol], mut base: LocalId) -> LocalId {
        for param in params {
            let param = self.canon_rigid(*param);
            self.param_witnesses.insert(param, (base, base + 1));
            base += 2;
            for protocol in self.program_builder.rigid_constraints(param) {
                let count = self
                    .program_builder
                    .protocol_requirements(protocol.protocol)
                    .map(|requirements| requirements.len())
                    .unwrap_or(0);
                let locals: Vec<LocalId> = (0..count)
                    .map(|ix| base + u16::try_from(ix).unwrap_or_default())
                    .collect();
                base += u16::try_from(count).unwrap_or_default();
                self.param_requirements
                    .insert((param, protocol.protocol), locals);
            }
        }
        base
    }

    /// Push one rigid generic's hidden block from this frame's own
    /// witnesses and dictionaries — the forwarding side of
    /// `bind_witness_params`'s layout.
    fn push_witness_block(
        &mut self,
        param: Symbol,
        operands: &mut Vec<Operand>,
        span: Span,
    ) -> Result<(), BackendError> {
        let param = self.canon_rigid(param);
        let Some((drop_witness, retain_witness)) = self.param_witnesses.get(&param).copied() else {
            return Err(BackendError::unsupported(
                "a generic value cannot cross this boundary without its ownership witnesses (not supported yet)"
                    .into(),
                span,
            ));
        };
        operands.push(Operand::Local(drop_witness));
        operands.push(Operand::Local(retain_witness));
        for protocol in self.program_builder.rigid_constraints(param) {
            let Some(locals) = self
                .param_requirements
                .get(&(param, protocol.protocol))
                .cloned()
            else {
                return Err(BackendError::unsupported(
                    "a generic value cannot cross this boundary without its conformance dictionaries (not supported yet)"
                        .into(),
                    span,
                ));
            };
            operands.extend(locals.into_iter().map(Operand::Local));
        }
        Ok(())
    }

    /// This frame's witnesses in symbol order — the deterministic layout
    /// closures use when inheriting them through their environments.
    fn sorted_witnesses(&self) -> Vec<(Symbol, (LocalId, LocalId))> {
        let mut all: Vec<(Symbol, (LocalId, LocalId))> = self
            .param_witnesses
            .iter()
            .map(|(symbol, pair)| (*symbol, *pair))
            .collect();
        all.sort_by_key(|(symbol, _)| *symbol);
        all
    }

    /// Append the callee instance's hidden witness arguments: the
    /// `[drop, retain]` pair for each rigid effect-generic its
    /// substitution mentions, supplied from this frame's own witnesses.
    fn append_witness_args(
        &mut self,
        func: FuncId,
        operands: &mut Vec<Operand>,
        span: Span,
    ) -> Result<(), BackendError> {
        let params = self
            .program_builder
            .instance_witnesses
            .get(&func)
            .cloned()
            .unwrap_or_default();
        for param in params {
            self.push_witness_block(param, operands, span)?;
        }
        Ok(())
    }

    fn types(&self) -> &'a crate::types::output::TypeOutput {
        self.program_builder.programs[self.program].program.types()
    }

    /// The wave-2 Copy gate: scalars, tuples of Copy types, and non-linear
    /// enums may exist as executable values. Everything else stays
    /// explicitly rejected until its wave.
    fn check_copy(&self, ty: &Ty, span: Span) -> Result<(), BackendError> {
        match ty {
            // An unconstrained solver variable means the value is never
            // used in a way that constrains it (a discarded intrinsic
            // result); nothing to move, drop, or read.
            Ty::Var(_) => Ok(()),
            // Function values copy freely; their captures are borrows.
            Ty::Func(_, _, _) => Ok(()),
            // A rigid effect-generic payload passes through registers
            // opaquely (a generic clause handles every instantiation); v1
            // restricts such payloads to Copy shapes.
            Ty::Param(_) => Ok(()),
            // Existential values carry their own drop/retain witnesses.
            Ty::Any { .. } => Ok(()),
            // Static arguments are phase-only (ADR 0035): evidence erases,
            // nothing exists at runtime.
            Ty::Static(_) => Ok(()),
            Ty::Borrow(_, inner) => self.check_copy(inner, span),
            Ty::Tuple(items) => {
                for item in items {
                    self.check_copy(item, span)?;
                }
                Ok(())
            }
            // Closed record rows lay out as label-sorted tuples.
            Ty::Record(row) if row.tail.is_none() => {
                for (_, item) in &row.fields {
                    self.check_copy(item, span)?;
                }
                Ok(())
            }
            Ty::Nominal(symbol, args) => {
                if scalar_ty(ty, span).is_ok() {
                    return Ok(());
                }
                if let Some((def, _)) = self.program_builder.enum_def(*symbol) {
                    let _ = def;
                    for arg in args {
                        if !matches!(arg, Ty::Eff(_) | Ty::Static(_)) {
                            self.check_copy(arg, span)?;
                        }
                    }
                    return Ok(());
                }
                if let Some((def, _)) = self.program_builder.struct_def(*symbol) {
                    let _ = def;
                    for arg in args {
                        if !matches!(arg, Ty::Eff(_) | Ty::Static(_)) {
                            self.check_copy(arg, span)?;
                        }
                    }
                    return Ok(());
                }
                Err(BackendError::unsupported(
                    format!(
                        "values of type `{}` are not supported yet",
                        ty.render_mono()
                    ),
                    span,
                ))
            }
            _ => scalar_ty(ty, span).map(|_| ()),
        }
    }

    /// A body node's baked type: canonicalized against the body's module,
    /// instantiated through this instance's substitution, and with
    /// associated-type projections reduced through the merged conformance
    /// table.
    fn resolved(&self, ty: &Ty) -> Ty {
        let module = self.program_builder.programs[self.program].module;
        // Uniqueness (`*T`) is a checking-time qualifier: the checker
        // enforced sole ownership; the representation is the inner type.
        struct StripUnique;
        impl crate::types::ty::TyFold for StripUnique {
            fn fold_ty(&mut self, ty: &Ty) -> Ty {
                match ty {
                    Ty::Unique(inner) => self.fold_ty(inner),
                    other => self.fold_children(other),
                }
            }
        }
        let ty = crate::types::ty::TyFold::fold_ty(&mut StripUnique, ty);
        let ty = canonical_ty(&ty, module);
        let ty = if self.subst.is_empty() {
            ty
        } else {
            ty.substitute(&self.subst, &FxHashMap::default(), &FxHashMap::default())
        };
        // Projections reduce only over var-free types: a foreign solver
        // variable has no slot in a scratch store. `normalize_ty` reduces
        // heads; the fold applies it at every depth.
        if ty_has_projection(&ty) && !ty_has_var(&ty) {
            struct DeepNormalize<'c> {
                catalog: &'c crate::types::catalog::TypeCatalog,
            }
            impl crate::types::ty::TyFold for DeepNormalize<'_> {
                fn fold_ty(&mut self, ty: &Ty) -> Ty {
                    let reduced = if matches!(ty, Ty::Proj(_, _, _)) {
                        let mut scratch = crate::types::solve::VarStore::default();
                        crate::types::solve::normalize_ty(&mut scratch, self.catalog, ty)
                    } else {
                        ty.clone()
                    };
                    self.fold_children(&reduced)
                }
            }
            return crate::types::ty::TyFold::fold_ty(
                &mut DeepNormalize {
                    catalog: &self.program_builder.catalog,
                },
                &ty,
            );
        }
        ty
    }

    /// The concrete type behind an inline-IR type annotation: resolved
    /// annotation symbols instantiate through this instance's substitution.
    fn annotation_value_ty(
        &self,
        annotation: &crate::node_kinds::type_annotation::TypeAnnotation,
        span: Span,
    ) -> Result<Ty, BackendError> {
        use crate::node_kinds::type_annotation::TypeAnnotationKind;
        match &annotation.kind {
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(symbol, _),
                ..
            } => {
                if let Some(ty) = self.subst.get(symbol) {
                    return Ok(ty.clone());
                }
                Ok(Ty::Nominal(
                    canonical(*symbol, self.program_builder.programs[self.program].module),
                    vec![],
                ))
            }
            TypeAnnotationKind::Borrow { inner, .. } => self.annotation_value_ty(inner, span),
            _ => Err(BackendError::unsupported(
                "this inline IR type annotation is not supported yet".into(),
                span,
            )),
        }
    }

    fn annotation_mem_ty(
        &self,
        annotation: &crate::node_kinds::type_annotation::TypeAnnotation,
        span: Span,
    ) -> Result<MemTy, BackendError> {
        let ty = self.annotation_value_ty(annotation, span)?;
        Ok(mem_ty_of(&ty))
    }

    /// Structurally add one reference per refcounted buffer the value owns
    /// (a RawPtr field IS a buffer; the mirror of structural teardown).
    fn retain_value(&mut self, value: Operand, ty: &Ty, span: Span) -> Result<(), BackendError> {
        let mut ty = ty.clone();
        while let Ty::Borrow(_, inner) = ty {
            ty = *inner;
        }
        match &ty {
            Ty::Any { .. } => {
                let witness = self.fresh_local();
                self.push(Inst::ExistentialWitness {
                    dest: witness,
                    src: value,
                    index: 1,
                });
                let payload = self.fresh_local();
                self.push(Inst::ExistentialPayload {
                    dest: payload,
                    src: value,
                });
                let dest = self.fresh_local();
                self.push(Inst::CallIndirect {
                    dest,
                    callee: Operand::Local(witness),
                    args: vec![Operand::Local(payload)],
                    unwind: None,
                });
                Ok(())
            }
            Ty::Param(symbol) => {
                // Native value; duplicate through the frame's retain
                // witness (value-witness-table passing).
                let Some((_, retain_witness)) =
                    self.param_witnesses.get(&self.canon_rigid(*symbol)).copied()
                else {
                    return Err(BackendError::unsupported(
                        "a generic value cannot be retained here without its ownership witnesses (not supported yet)"
                            .into(),
                        span,
                    ));
                };
                let dest = self.fresh_local();
                self.push(Inst::CallIndirect {
                    dest,
                    callee: Operand::Local(retain_witness),
                    args: vec![value],
                    unwind: None,
                });
                Ok(())
            }
            Ty::Nominal(symbol, _) if *symbol == Symbol::RawPtr => {
                self.push(Inst::RetainPtr { src: value });
                Ok(())
            }
            Ty::Nominal(symbol, args) => {
                // A `'heap` handle duplicates as a region claim; its
                // interior belongs to the region (structural recursion
                // through a recursive node type would never terminate).
                if self
                    .program_builder
                    .struct_def(*symbol)
                    .is_some_and(|(def, _)| def.heap)
                {
                    self.push(Inst::RegionAcquire { src: value });
                    return Ok(());
                }
                let Some(fields) = self.program_builder.field_types(*symbol, args) else {
                    // Enum retains dispatch on the tag, one arm per variant
                    // with buffer-carrying payloads; scalars retain nothing.
                    if let Some(payloads) = self.program_builder.variant_payloads(*symbol, args) {
                        self.retain_enum_value(value, payloads, span)?;
                    }
                    return Ok(());
                };
                for (index, field_ty) in fields.iter().enumerate() {
                    if !donates(self.program_builder, field_ty) {
                        continue;
                    }
                    let field = self.fresh_local();
                    self.push(Inst::GetField {
                        dest: field,
                        src: value,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    self.retain_value(Operand::Local(field), field_ty, span)?;
                }
                Ok(())
            }
            Ty::Tuple(items) => {
                for (index, item_ty) in items.iter().enumerate() {
                    if !donates(self.program_builder, item_ty) {
                        continue;
                    }
                    let item = self.fresh_local();
                    self.push(Inst::TupleGet {
                        dest: item,
                        src: value,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    self.retain_value(Operand::Local(item), item_ty, span)?;
                }
                Ok(())
            }
            Ty::Record(row) => {
                for (index, (_, item_ty)) in row.fields.iter().enumerate() {
                    if !donates(self.program_builder, item_ty) {
                        continue;
                    }
                    let item = self.fresh_local();
                    self.push(Inst::TupleGet {
                        dest: item,
                        src: value,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    self.retain_value(Operand::Local(item), item_ty, span)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Compile a run of nodes; the value is the final expression's, or
    /// Unit. Unconsumed owned temporaries drop at each statement boundary
    /// (structural temp drops, ADR 0017), except the final value.
    fn compile_nodes(&mut self, nodes: &[&Node]) -> Result<Operand, BackendError> {
        let mut value = Operand::Const(Constant::Unit);
        let last = nodes.len().saturating_sub(1);
        for (ix, node) in nodes.iter().enumerate() {
            // Each statement flushes only its own temporaries: temps
            // registered by the enclosing context (a match arm's owned
            // bindings) outlive inner statement boundaries.
            let floor = self.stmt_temps.len();
            value = self.compile_node(node)?;
            if ix != last {
                self.flush_stmt_temps_above(floor, None);
                value = Operand::Const(Constant::Unit);
            } else {
                self.flush_stmt_temps_above(floor, Some(value));
            }
        }
        Ok(value)
    }

    /// CHG-06: v1 closure captures are Copy values only. Handler clauses
    /// (extent-bounded shared borrows) do not pass through here. A closure
    /// capturing an owned buffer or region handle could outlive it.
    fn check_captures(&self, captured: &[Symbol], span: Span) -> Result<(), BackendError> {
        for symbol in captured {
            let Some(local) = self.locals.get(symbol).copied() else {
                continue;
            };
            let owning = self
                .owned_tys
                .get(&local)
                .or_else(|| self.local_tys.get(&local))
                .is_some_and(|ty| {
                    let mut ty = ty;
                    while let Ty::Borrow(_, inner) = ty {
                        ty = inner;
                    }
                    contains_buffer(self.program_builder, ty)
                        || contains_object(self.program_builder, ty)
                });
            if owning {
                return Err(BackendError::unsupported(
                    "capturing owned values in function values is not supported yet".into(),
                    span,
                ));
            }
        }
        Ok(())
    }

    /// Re-bind celled parameters through cells (assignment conversion
    /// for parameters shared mutably with this frame's closures).
    fn cell_celled_params(&mut self, params: &[crate::typed_ast::Parameter]) {
        for param in params {
            let Name::Resolved(symbol, _) = &param.name else {
                continue;
            };
            if !self.celled.contains(symbol) {
                continue;
            }
            let Some(local) = self.locals.get(symbol).copied() else {
                continue;
            };
            let handle = self.fresh_local();
            self.push(Inst::CellNew {
                dest: handle,
                init: Operand::Local(local),
            });
            self.locals.insert(*symbol, handle);
            self.cell_handles.insert(handle);
        }
    }

    /// Enforce an explicit capture list (the reference's rules): every
    /// free variable must be listed; `copy` requires a copyable type;
    /// `consuming` moves the owner. Owned (droppable) payloads wait on
    /// closure drop glue and borrow pinning waits on the flow-rule
    /// port, so those modes accept copyable referents only for now.
    fn check_capture_list(&mut self, func: &Func, captured: &[Symbol]) -> Result<(), BackendError> {
        use crate::node_kinds::func::CaptureMode;
        for spec in &func.captures {
            let Ok(symbol) = spec.name.symbol() else {
                continue;
            };
            let Some(local) = self.locals.get(&symbol).copied() else {
                continue;
            };
            let ty = self
                .owned_tys
                .get(&local)
                .or_else(|| self.local_tys.get(&local))
                .cloned()
                .unwrap_or(Ty::Error);
            let droppable = self.needs_release(&ty);
            match spec.mode {
                CaptureMode::Copy => {
                    if droppable {
                        return Err(BackendError::unsupported(
                            format!(
                                "cannot capture `{}` by copy: copy captures require a copyable type",
                                spec.name.name_str()
                            ),
                            spec.span,
                        ));
                    }
                }
                CaptureMode::Move => {
                    if droppable {
                        return Err(BackendError::unsupported(
                            format!(
                                "consuming captures of owned values are not supported yet (`{}`)",
                                spec.name.name_str()
                            ),
                            spec.span,
                        ));
                    }
                    // The closure owns the value now; later uses in the
                    // frame are uses of a moved value.
                    self.moved.insert(local);
                }
                CaptureMode::BorrowShared | CaptureMode::BorrowMut => {
                    if droppable {
                        return Err(BackendError::unsupported(
                            format!(
                                "borrow captures of owned values are not supported yet (`{}`)",
                                spec.name.name_str()
                            ),
                            spec.span,
                        ));
                    }
                }
            }
        }
        for symbol in captured {
            let listed = func
                .captures
                .iter()
                .any(|spec| spec.name.symbol().ok() == Some(*symbol));
            if !listed {
                return Err(BackendError::new(
                    "cannot implicitly capture a value once the closure names an explicit capture list; add it to the list"
                        .into(),
                    func.body.span,
                ));
            }
        }
        Ok(())
    }

    /// Compile a block in its own drop scope. The block's value escapes the
    /// scope to the enclosing statement; everything else the scope owns
    /// drops here, in reverse declaration order.
    fn compile_block(&mut self, block: &Block) -> Result<Operand, BackendError> {
        self.scopes.push(Vec::new());
        let nodes: Vec<&Node> = block.body.iter().collect();
        let value = self.compile_nodes(&nodes)?;

        if !self.terminated()
            && let Operand::Local(local) = value
            && let Some(scope) = self.scopes.last_mut()
            && let Some(position) = scope.iter().position(|owned| *owned == local)
        {
            // The value moves out to the enclosing statement.
            scope.remove(position);
            self.stmt_temps.push(local);
        }
        self.scopes.pop();
        Ok(value)
    }

    fn compile_node(&mut self, node: &Node) -> Result<Operand, BackendError> {
        match node {
            Node::Expr(expr) => self.compile_expr(expr),
            Node::Stmt(stmt) => self.compile_stmt(stmt),
            Node::Decl(decl) => self.compile_decl(decl),
        }
    }

    fn compile_decl(&mut self, decl: &Decl) -> Result<Operand, BackendError> {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                rhs,
                type_annotation,
                ..
            } => {
                let Some(rhs) = rhs else {
                    return Err(BackendError::unsupported(
                        "`let` without an initializer is not supported yet".into(),
                        decl.span,
                    ));
                };
                // `consume` of a borrowed source drains a retained copy:
                // the owner is always protected by the reference the
                // donation takes here (rule 3 of
                // docs/ownership-rethink-plan.md — the old rejection
                // guarded an implementation detail that no longer
                // exists). The donation happens in consume_binding
                // below, which sees the owned destination type.
                // A borrow-annotated binding (`let b: &T = s`) is a loan:
                // the source keeps ownership and is not moved.
                if let Some(annotation) = type_annotation
                    && let crate::node_kinds::type_annotation::TypeAnnotationKind::Borrow {
                        mutable,
                        ..
                    } = &annotation.kind
                    && let PatternKind::Bind(Name::Resolved(symbol, bind_name)) = &lhs.kind
                {
                    let value = self.compile_expr(rhs)?;
                    let local = self.fresh_local();
                    self.push(Inst::Copy {
                        dest: local,
                        src: value,
                    });
                    self.record_view(Operand::Local(local), value);
                    self.view_locals.insert(local);
                    if let Operand::Local(source) = value {
                        let root = self.borrow_root(source);
                        self.loans.push(Loan {
                            view_symbol: *symbol,
                            view_name: bind_name.clone(),
                            root,
                            exclusive: *mutable,
                            loop_depth: self.loop_stack.len(),
                        });
                    }
                    self.locals.insert(*symbol, local);
                    self.local_tys.insert(
                        local,
                        Ty::Borrow(Perm::Shared, Box::new(self.resolved(&rhs.ty))),
                    );
                    return Ok(Operand::Const(Constant::Unit));
                }
                // letrec: a func-valued binding that captures frame
                // locals and is referenced from a nested function (its
                // own body, or a sibling closure declared later) binds
                // through a cell created before the closure compiles.
                if let PatternKind::Bind(Name::Resolved(symbol, _)) = &lhs.kind
                    && let ExprKind::Func(func) = &rhs.kind
                    && self.nested_refs.contains(symbol)
                {
                    let body_nodes: Vec<&Node> = func.body.body.iter().collect();
                    if !free_locals(&body_nodes, &self.locals).is_empty()
                        || !func.captures.is_empty()
                    {
                        if !func.scheme.params.is_empty() {
                            // A closure compiles once against this
                            // frame; it cannot specialize per call.
                            return Err(BackendError::unsupported(
                                "generic local functions that capture are not supported yet".into(),
                                decl.span,
                            ));
                        }
                        let handle = self.fresh_local();
                        self.push(Inst::CellNew {
                            dest: handle,
                            init: Operand::Const(Constant::Unit),
                        });
                        self.locals.insert(*symbol, handle);
                        self.cell_handles.insert(handle);
                        let closure = self.compile_closure(func, &rhs.ty)?;
                        self.push(Inst::CellSet {
                            cell: Operand::Local(handle),
                            src: closure,
                        });
                        return Ok(Operand::Const(Constant::Unit));
                    }
                }
                let value = self.compile_expr(rhs)?;
                let ty = self.resolved(&rhs.ty);
                self.bind_owned_pattern(lhs, value, &ty)?;
                Ok(Operand::Const(Constant::Unit))
            }
            // Named functions desugar to func-valued lets before
            // resolution; a bare Func decl only remains for callables
            // compiled on demand when called.
            DeclKind::Func(_) => Ok(Operand::Const(Constant::Unit)),
            _ => Err(BackendError::unsupported(
                "this declaration is not supported yet".into(),
                decl.span,
            )),
        }
    }

    /// Bind a `let` pattern, transferring ownership of the initializer.
    fn bind_owned_pattern(
        &mut self,
        pattern: &Pattern,
        value: Operand,
        ty: &Ty,
    ) -> Result<(), BackendError> {
        match &pattern.kind {
            PatternKind::Bind(Name::Resolved(symbol, _)) => {
                if self.celled.contains(symbol) {
                    // Assignment-converted: the binding becomes a cell
                    // shared with the closures that capture it. Cell
                    // contents stay copyable; ownership-sensitive
                    // mutable captures need explicit modes.
                    if self.needs_release(ty) {
                        return Err(BackendError::unsupported(
                            "cannot capture an ownership-sensitive mutable value in a function value (not supported yet)"
                                .into(),
                            pattern.span,
                        ));
                    }
                    let handle = self.fresh_local();
                    self.push(Inst::CellNew {
                        dest: handle,
                        init: value,
                    });
                    self.consume_binding(value, ty, pattern.span)?;
                    self.locals.insert(*symbol, handle);
                    self.local_tys.insert(handle, ty.clone());
                    self.cell_handles.insert(handle);
                    return Ok(());
                }
                // An owned rvalue temporary becomes the binding's storage
                // directly: a `let` is a name for a value, not a copy of
                // one (wave 11a copy folding — the straight-line half of
                // SSA construction, Braun et al., CC 2013). Only frame-
                // owned temporaries alias; a parameter or another
                // binding's local keeps its own storage.
                let local = if let Operand::Local(source) = value
                    && source >= self.param_floor
                    && self.stmt_temps.contains(&source)
                {
                    source
                } else {
                    let local = self.fresh_local();
                    self.push(Inst::Copy {
                        dest: local,
                        src: value,
                    });
                    local
                };
                self.locals.insert(*symbol, local);
                self.local_tys.insert(local, ty.clone());
                self.propagate_view(Operand::Local(local), value);
                if contains_borrow_classified(self.program_builder, ty) {
                    self.view_locals.insert(local);
                }
                if let Operand::Local(source) = value
                    && self.borrow_roots.contains_key(&source)
                    && borrow_classified(self.program_builder, ty)
                    && let PatternKind::Bind(Name::Resolved(_, bind_name)) = &pattern.kind
                {
                    let root = self.borrow_root(source);
                    self.loans.push(Loan {
                        view_symbol: *symbol,
                        view_name: bind_name.clone(),
                        root,
                        exclusive: false,
                        loop_depth: self.loop_stack.len(),
                    });
                }
                // Register with the value's concrete type when the
                // aliased temporary carries one: a desugared binding's
                // pattern type can be an unreduced projection (a
                // for-loop's iterator), which the release classifier
                // cannot see through.
                let value_ty = match value {
                    Operand::Local(source) => self.owned_tys.get(&source).cloned(),
                    _ => None,
                };
                self.consume_binding(value, ty, pattern.span)?;
                self.own_local(local, value_ty.as_ref().unwrap_or(ty));
                Ok(())
            }
            PatternKind::Wildcard => {
                // `let _ = value` still consumes: drop it now.
                self.consume_binding(value, ty, pattern.span)?;
                self.drop_value(value, ty);
                Ok(())
            }
            PatternKind::Tuple(elements) => {
                let element_tys = tuple_element_tys(ty, elements.len());
                let extracted = self.extract_tuple(value, elements.len());
                // Deconstruction: when the source is owned, its elements
                // inherit that ownership (binds must not also donate);
                // a borrowed source keeps ownership and binds donate.
                if self.consume_operand(value) {
                    for (operand, element_ty) in extracted.iter().zip(&element_tys) {
                        if let Operand::Local(local) = operand {
                            self.produce_temp(*local, element_ty);
                        }
                    }
                }
                for ((element, extracted), element_ty) in
                    elements.iter().zip(extracted).zip(&element_tys)
                {
                    self.bind_owned_pattern(element, extracted, element_ty)?;
                }
                Ok(())
            }
            PatternKind::Record { fields } => {
                let cells = self.record_cells(pattern, fields, ty)?;
                let extracted = self.extract_tuple(value, cells.len());
                if self.consume_operand(value) {
                    for (operand, cell) in extracted.iter().zip(&cells) {
                        if let Operand::Local(local) = operand {
                            self.produce_temp(*local, &cell.field_ty);
                        }
                    }
                }
                for (cell, slot) in cells.iter().zip(extracted) {
                    let Some(name) = &cell.bind else {
                        self.bind_owned_pattern(&cell.pattern, slot, &cell.field_ty)?;
                        continue;
                    };
                    // `label: pattern` binds both names to the slot; two
                    // owners of one owned value cannot both be real.
                    if self.needs_release(&cell.field_ty) {
                        return Err(BackendError::unsupported(
                            "record destructuring that binds both a field and its interior of an owned value is not supported yet"
                                .into(),
                            pattern.span,
                        ));
                    }
                    let bind = Pattern {
                        id: cell.pattern.id,
                        kind: PatternKind::Bind(name.clone()),
                        span: pattern.span,
                    };
                    self.bind_owned_pattern(&bind, slot, &cell.field_ty)?;
                    self.bind_owned_pattern(&cell.pattern, slot, &cell.field_ty)?;
                }
                Ok(())
            }
            PatternKind::Struct {
                fields,
                field_names,
                ..
            } => {
                let (heap, cells) = self.struct_cells(pattern, fields, field_names, ty)?;
                if heap {
                    // Heap fields are views of the object: binds donate a
                    // reference on the way in, unmentioned fields stay the
                    // object's, and the object's own drop releases the
                    // stored references exactly once.
                    let consumed = self.consume_operand(value);
                    for (index, cell) in cells.iter().enumerate() {
                        if matches!(cell.pattern.kind, PatternKind::Wildcard) {
                            continue;
                        }
                        let slot = self.fresh_local();
                        self.push(Inst::ObjectGet {
                            dest: slot,
                            src: value,
                            index: u16::try_from(index).unwrap_or_default(),
                        });
                        if self.needs_release(&cell.field_ty) {
                            self.retain_value(
                                Operand::Local(slot),
                                &cell.field_ty,
                                pattern.span,
                            )?;
                            self.produce_temp(slot, &cell.field_ty);
                        }
                        self.bind_owned_pattern(
                            &cell.pattern,
                            Operand::Local(slot),
                            &cell.field_ty,
                        )?;
                    }
                    if consumed {
                        self.drop_value(value, ty);
                    }
                    return Ok(());
                }
                let extracted = self.extract_struct_fields(value, false, cells.len());
                if self.consume_operand(value) {
                    for (operand, cell) in extracted.iter().zip(&cells) {
                        if let Operand::Local(local) = operand {
                            self.produce_temp(*local, &cell.field_ty);
                        }
                    }
                }
                for (cell, slot) in cells.iter().zip(extracted) {
                    self.bind_owned_pattern(&cell.pattern, slot, &cell.field_ty)?;
                }
                Ok(())
            }
            _ => Err(BackendError::unsupported(
                "destructuring patterns are not supported yet".into(),
                pattern.span,
            )),
        }
    }

    fn compile_stmt(&mut self, stmt: &Stmt) -> Result<Operand, BackendError> {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.compile_expr(expr),
            StmtKind::Return(expr) => {
                let value = match expr {
                    Some(expr) => self.compile_expr(expr)?,
                    None => Operand::Const(Constant::Unit),
                };
                self.emit_return(value);
                Ok(Operand::Const(Constant::Unit))
            }
            StmtKind::If(cond, then_block, else_block) => {
                // Statement-position `if` still carries its blocks' values:
                // in tail position the enclosing block's value is this
                // statement's.
                let cond = self.compile_expr(cond)?;
                let result = self.fresh_local();
                let then_id = self.new_block();
                let join = self.new_block();
                let else_id = self.new_block();
                self.terminate(Term::Branch {
                    cond,
                    then_block: then_id,
                    else_block: else_id,
                });
                let moved_before = self.moved.clone();
                let globals_before = self.moved_globals.clone();
                let temps_before = self.stmt_temps.clone();
                let mut arm_ends: Vec<ArmEnd> = Vec::new();

                self.switch_to(then_id);
                let value = self.compile_block(then_block)?;
                if !self.terminated() {
                    arm_ends.push(ArmEnd {
                        block: self.current,
                        value,
                        moved: std::mem::take(&mut self.moved),
                        moved_globals: std::mem::take(&mut self.moved_globals),
                        temps: std::mem::take(&mut self.stmt_temps),
                    });
                }
                if let Some(else_block) = else_block {
                    self.switch_to(else_id);
                    self.moved = moved_before.clone();
                    self.moved_globals = globals_before.clone();
                    self.stmt_temps = temps_before.clone();
                    let value = self.compile_block(else_block)?;
                    if !self.terminated() {
                        arm_ends.push(ArmEnd {
                            block: self.current,
                            value,
                            moved: std::mem::take(&mut self.moved),
                            moved_globals: std::mem::take(&mut self.moved_globals),
                            temps: std::mem::take(&mut self.stmt_temps),
                        });
                    }
                } else {
                    // The fall-through path joins with a Unit value.
                    arm_ends.push(ArmEnd {
                        block: else_id,
                        value: Operand::Const(Constant::Unit),
                        moved: moved_before.clone(),
                        moved_globals: globals_before.clone(),
                        temps: temps_before.clone(),
                    });
                }
                // The merged value is a tracked temporary like any other
                // rvalue: a statement-position `if` whose arms produce a
                // droppable value (a mut call's returned view, say) must
                // hand it to the release planner, not strand it in the
                // join parameter.
                let result_ty = arm_ends.iter().find_map(|arm| match arm.value {
                    Operand::Local(local) => self.owned_tys.get(&local).cloned(),
                    _ => None,
                });
                self.merge_arms(arm_ends, result, join, temps_before, moved_before);
                if let Some(ty) = result_ty {
                    self.produce_temp(result, &ty);
                }
                Ok(Operand::Local(result))
            }
            StmtKind::Loop(cond, body) => {
                let header = self.new_block();
                let body_id = self.new_block();
                let normal_exit = self.new_block();
                let exit = self.new_block();
                let moved_before = self.moved.clone();
                let globals_before = self.moved_globals.clone();
                let temps_before = self.stmt_temps.clone();
                self.terminate(Term::Goto(header, Vec::new()));
                self.switch_to(header);
                let mut condition_exits = false;
                match cond {
                    Some(cond) => {
                        let cond = self.compile_expr(cond)?;
                        condition_exits = true;
                        self.terminate(Term::Branch {
                            cond,
                            then_block: body_id,
                            else_block: normal_exit,
                        });
                    }
                    None => self.terminate(Term::Goto(body_id, Vec::new())),
                }
                self.switch_to(body_id);
                let outer_locals: rustc_hash::FxHashSet<LocalId> =
                    self.locals.values().copied().collect();
                self.loop_stack.push(LoopFrame {
                    header,
                    continues_moved: rustc_hash::FxHashSet::default(),
                    breaks: Vec::new(),
                });
                self.compile_block(body)?;
                let frame = self.loop_stack.pop().unwrap_or(LoopFrame {
                    header,
                    continues_moved: rustc_hash::FxHashSet::default(),
                    breaks: Vec::new(),
                });
                // The body's discarded tail value drops here, on the
                // back-edge: its register is assigned on every path that
                // reaches this point, unlike the exit block (a `break`
                // arrives there without running the tail).
                self.flush_stmt_temps(None);
                let mut body_end_moved = self.moved.clone();
                body_end_moved.extend(frame.continues_moved.iter().copied());
                // Loop-carried moves: a value moved on the looping path
                // is gone on re-entry; if the body also reads it, the
                // second iteration uses a moved value.
                let (_, _, body_uses) = cell_scan(&{
                    let nodes: Vec<&Node> = body.body.iter().collect();
                    nodes
                });
                for local in body_end_moved.difference(&moved_before) {
                    // Only values that outlive an iteration can carry:
                    // body-declared locals are fresh every pass.
                    if !outer_locals.contains(local) {
                        continue;
                    }
                    if let Some((symbol, _)) = self.locals.iter().find(|(_, bound)| *bound == local)
                        && body_uses.get(symbol).copied().unwrap_or(0) > 0
                    {
                        self.deferred_errors.push(BackendError::new(
                            "use of moved value: consumed on a previous loop iteration".into(),
                            body.span,
                        ));
                        break;
                    }
                }
                for slot in self.moved_globals.clone().difference(&globals_before) {
                    let uses_global = self
                        .program_builder
                        .global_slots
                        .iter()
                        .find(|(_, bound)| *bound == slot)
                        .is_some_and(|(symbol, _)| body_uses.get(symbol).copied().unwrap_or(0) > 0);
                    if uses_global {
                        self.deferred_errors.push(BackendError::new(
                            "use of moved value: consumed on a previous loop iteration".into(),
                            body.span,
                        ));
                        break;
                    }
                }
                self.terminate(Term::Goto(header, Vec::new()));
                // Merge every path into the exit: the condition's normal
                // exit (whose state is conservatively the union of entry
                // and back-edge states) plus each break's recorded state.
                let mut arm_ends = frame.breaks;
                if condition_exits {
                    self.switch_to(normal_exit);
                    let mut exit_moved = moved_before.clone();
                    exit_moved.extend(body_end_moved.iter().copied());
                    let mut exit_moved_globals = globals_before.clone();
                    exit_moved_globals.extend(self.moved_globals.iter().copied());
                    arm_ends.push(ArmEnd {
                        block: normal_exit,
                        value: Operand::Const(Constant::Unit),
                        moved: exit_moved,
                        moved_globals: exit_moved_globals,
                        temps: temps_before.clone(),
                    });
                } else {
                    self.switch_to(normal_exit);
                    self.terminate(Term::Trap("unreachable loop exit"));
                }
                let result = self.fresh_local();
                self.merge_arms(arm_ends, result, exit, temps_before, moved_before);
                Ok(Operand::Const(Constant::Unit))
            }
            StmtKind::Break => {
                let Some(_frame) = self.loop_stack.last() else {
                    return Err(BackendError::new(
                        "`break` outside a loop".into(),
                        stmt.span,
                    ));
                };
                // Record this path's end state for the loop-exit merge
                // (the relay block is where the merge appends this
                // path's divergent drops).
                let relay = self.new_block();
                self.terminate(Term::Goto(relay, Vec::new()));
                let moved = self.moved.clone();
                let temps = self.stmt_temps.clone();
                if let Some(frame) = self.loop_stack.last_mut() {
                    frame.breaks.push(ArmEnd {
                        block: relay,
                        value: Operand::Const(Constant::Unit),
                        moved,
                        moved_globals: self.moved_globals.clone(),
                        temps,
                    });
                }
                Ok(Operand::Const(Constant::Unit))
            }
            StmtKind::Resume(value) => {
                // `'continue v` resumes the enclosing handler's perform:
                // the clause returns v to the perform site (one-shot resume
                // as return), from any loop depth.
                if self.clause_delimiter.is_none() {
                    return Err(BackendError::new(
                        "`'continue` outside an effect handler".into(),
                        stmt.span,
                    ));
                }
                let value = match value {
                    Some(value) => self.compile_expr(value)?,
                    None => Operand::Const(Constant::Unit),
                };
                self.emit_frame_return(value);
                Ok(Operand::Const(Constant::Unit))
            }
            StmtKind::Continue => {
                let Some(frame) = self.loop_stack.last() else {
                    return Err(BackendError::new(
                        "`continue` outside a loop".into(),
                        stmt.span,
                    ));
                };
                let header = frame.header;
                let moved = self.moved.clone();
                if let Some(frame) = self.loop_stack.last_mut() {
                    frame.continues_moved.extend(moved);
                }
                self.terminate(Term::Goto(header, Vec::new()));
                Ok(Operand::Const(Constant::Unit))
            }
            StmtKind::Assignment(lhs, rhs) => {
                match &lhs.kind {
                    ExprKind::Variable(Name::Resolved(symbol, _)) => {
                        if !self.locals.contains_key(symbol)
                            && let Some(slot) =
                                self.program_builder.global_slots.get(symbol).copied()
                        {
                            let value = self.compile_expr(rhs)?;
                            let ty = self
                                .program_builder
                                .global_tys
                                .get(&slot)
                                .cloned()
                                .unwrap_or(Ty::Error);
                            // Reassignment restores a moved global.
                            self.moved_globals.remove(&slot);
                            if self.needs_release(&ty) {
                                let old = self.fresh_local();
                                self.push(Inst::GlobalLoad {
                                    dest: old,
                                    global: slot,
                                });
                                self.drop_value(Operand::Local(old), &ty);
                            }
                            self.consume_binding(value, &ty, rhs.span)?;
                            self.push(Inst::GlobalStore {
                                global: slot,
                                src: value,
                            });
                            return Ok(Operand::Const(Constant::Unit));
                        }
                        let Some(local) = self.locals.get(symbol).copied() else {
                            return Err(BackendError::unsupported(
                                "assignment to a non-local is not supported yet".into(),
                                lhs.span,
                            ));
                        };
                        // Shared loans never block a reassignment: the
                        // displaced value stays alive to scope exit, so
                        // the view keeps its snapshot.
                        if self.cell_handles.contains(&local) {
                            // Assignment-converted binding: write the
                            // shared cell (contents are copyable, so no
                            // old-value drop is due).
                            let value = self.compile_expr(rhs)?;
                            self.push(Inst::CellSet {
                                cell: Operand::Local(local),
                                src: value,
                            });
                            return Ok(Operand::Const(Constant::Unit));
                        }
                        if self.captured_locals.contains(&local) {
                            return Err(BackendError::unsupported(
                                "assignment to a captured value is not supported yet".into(),
                                lhs.span,
                            ));
                        }
                        let value = self.compile_expr(rhs)?;
                        // Replacement: the old value is destroyed exactly
                        // once before the new one lands (OWN-04) — or
                        // displaced to scope exit while a view is live.
                        if let Some(ty) = self.owned_tys.get(&local).cloned() {
                            if !self.moved.contains(&local) {
                                self.displace_or_drop(local, &ty);
                            }
                            self.moved.remove(&local);
                        }
                        self.consume_binding(value, &rhs.ty, rhs.span)?;
                        self.push(Inst::Copy {
                            dest: local,
                            src: value,
                        });
                        if self.owned_tys.contains_key(&local) {
                            self.record_flow(verify::FlowEvent::Def(local));
                        }
                        Ok(Operand::Const(Constant::Unit))
                    }
                    ExprKind::Proj(_, _, _) | ExprKind::Member(_, _) => {
                        let Some(chain) = self.resolve_place(lhs)? else {
                            return Err(BackendError::unsupported(
                                "assignment through this place is not supported yet".into(),
                                lhs.span,
                            ));
                        };
                        let value = self.compile_expr(rhs)?;
                        let value_ty = self.resolved(&rhs.ty);
                        self.write_place(&chain, value, &value_ty, rhs.span, true)?;
                        Ok(Operand::Const(Constant::Unit))
                    }
                    _ => Err(BackendError::unsupported(
                        "assignment to this place is not supported yet".into(),
                        lhs.span,
                    )),
                }
            }
            StmtKind::Handling { effect_name, body } => {
                let Name::Resolved(effect, _) = effect_name else {
                    return Err(BackendError::new(
                        "handler without a resolved effect".into(),
                        stmt.span,
                    ));
                };
                let effect = canonical(*effect, self.program_builder.programs[self.program].module);
                self.install_handler(effect, body)?;
                Ok(Operand::Const(Constant::Unit))
            }
        }
    }

    fn compile_expr(&mut self, expr: &Expr) -> Result<Operand, BackendError> {
        let operand = self.compile_expr_inner(expr)?;
        // The checker recorded an existential coercion here: pack the
        // concrete payload behind its witness table.
        if let Some(pack) = &expr.existential_pack {
            return self.compile_existential_pack(expr, pack, operand);
        }
        // The checker coerced this borrowed use into an owned one through
        // an implicit CheapClone (`coerce_clones`): one reference per
        // owned buffer.
        if expr.ownership.auto_clone {
            let ty = self.resolved(&expr.ty);
            if contains_buffer(self.program_builder, &ty) {
                let dest = self.fresh_local();
                self.push(Inst::Copy { dest, src: operand });
                let mut retained = ty.clone();
                while let Ty::Borrow(_, inner) = retained {
                    retained = *inner;
                }
                self.retain_value(Operand::Local(dest), &retained, expr.span)?;
                self.produce_temp(dest, &retained);
                return Ok(Operand::Local(dest));
            }
        }
        Ok(operand)
    }

    fn compile_expr_inner(&mut self, expr: &Expr) -> Result<Operand, BackendError> {
        let ty = self.resolved(&expr.ty);
        self.check_copy(&ty, expr.span)?;
        match &expr.kind {
            ExprKind::Lit(literal) => self.compile_literal(expr, literal),
            ExprKind::Tuple(items) if items.is_empty() => Ok(Operand::Const(Constant::Unit)),
            ExprKind::Tuple(items) => {
                let args = items
                    .iter()
                    .map(|item| self.compile_expr(item))
                    .collect::<Result<Vec<_>, _>>()?;
                // Consume with the tuple's own element types: the
                // container owns its slots, so a borrowed source (a
                // borrowed parameter, a view) donates a reference here
                // instead of slipping in unretained and double-freeing
                // when the container is decomposed (rule 2 of
                // docs/ownership-rethink-plan.md).
                let element_tys = tuple_element_tys(&ty, items.len());
                for ((arg, item), element_ty) in args.iter().zip(items).zip(&element_tys) {
                    let dest_ty = if matches!(element_ty, Ty::Error) {
                        item.ty.clone()
                    } else {
                        // The slot owns whatever its declared borrows
                        // point at (owning stored views): strip so the
                        // donation machinery sees the inner type, in
                        // step with the stripping drop walks.
                        strip_borrows(element_ty.clone())
                    };
                    self.consume_binding(*arg, &dest_ty, item.span)?;
                }
                let dest = self.fresh_local();
                // A container wrapping a view inherits its provenance.
                for arg in &args {
                    self.propagate_view(Operand::Local(dest), *arg);
                }
                self.push(Inst::Tuple { dest, args });
                self.produce_temp(dest, &ty);
                Ok(Operand::Local(dest))
            }
            ExprKind::Con {
                enum_symbol,
                tag,
                args,
                ..
            } => {
                let enum_symbol = canonical(
                    *enum_symbol,
                    self.program_builder.programs[self.program].module,
                );
                let compiled = args
                    .iter()
                    .map(|arg| self.compile_expr(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                // Destination-typed consumption, as for tuples: the
                // payload slot owns its value, so borrowed sources
                // donate a reference on the way in.
                let payload_tys = self
                    .program_builder
                    .variant_payloads(enum_symbol, head_args(&ty))
                    .and_then(|payloads| payloads.into_iter().nth(usize::from(*tag)));
                for (index, (operand, arg)) in compiled.iter().zip(args).enumerate() {
                    let dest_ty = payload_tys
                        .as_ref()
                        .and_then(|tys| tys.get(index))
                        .cloned()
                        .map(strip_borrows)
                        .unwrap_or_else(|| arg.ty.clone());
                    self.consume_binding(*operand, &dest_ty, arg.span)?;
                }
                let dest = self.fresh_local();
                for operand in &compiled {
                    self.propagate_view(Operand::Local(dest), *operand);
                }
                self.push(Inst::Variant {
                    dest,
                    enum_symbol,
                    tag: *tag,
                    args: compiled,
                });
                self.produce_temp(dest, &ty);
                Ok(Operand::Local(dest))
            }
            ExprKind::Proj(base, _, field) => {
                let base_ty = self.resolved(&base.ty);
                let mut head = &base_ty;
                while let Ty::Borrow(_, inner) = head {
                    head = inner;
                }
                let Ty::Nominal(struct_symbol, _) = head else {
                    return Err(BackendError::unsupported(
                        "field reads on this type are not supported yet".into(),
                        expr.span,
                    ));
                };
                let struct_symbol = canonical(
                    *struct_symbol,
                    self.program_builder.programs[self.program].module,
                );
                let field = canonical(*field, self.program_builder.programs[self.program].module);
                let Some(index) = self.program_builder.field_index(struct_symbol, field) else {
                    return Err(BackendError::new(
                        "stored field without a declaration index".into(),
                        expr.span,
                    ));
                };
                let heap = self
                    .program_builder
                    .struct_def(struct_symbol)
                    .is_some_and(|(def, _)| def.heap);
                let src = self.compile_expr(base)?;
                let dest = self.fresh_local();
                if heap {
                    self.push(Inst::ObjectGet { dest, src, index });
                } else {
                    self.push(Inst::GetField { dest, src, index });
                }
                // Field reads carry their owner's provenance so views
                // derived from fields track the whole value.
                self.record_view(Operand::Local(dest), src);
                Ok(Operand::Local(dest))
            }
            ExprKind::Member(Some(receiver), crate::label::Label::Positional(index)) => {
                let src = self.compile_expr(receiver)?;
                let index = u16::try_from(*index)
                    .map_err(|_| BackendError::new("tuple index out of range".into(), expr.span))?;
                let dest = self.fresh_local();
                self.push(Inst::TupleGet { dest, src, index });
                Ok(Operand::Local(dest))
            }
            // A record field read: the label's position in the row is its
            // slot (rows keep fields label-sorted, fixing the layout).
            ExprKind::Member(Some(receiver), crate::label::Label::Named(name))
                if matches!(strip_borrows(self.resolved(&receiver.ty)), Ty::Record(_)) =>
            {
                let Ty::Record(row) = strip_borrows(self.resolved(&receiver.ty)) else {
                    unreachable!()
                };
                let index = row
                    .fields
                    .iter()
                    .position(|(label, _)| {
                        matches!(label, crate::label::Label::Named(field) if field == name)
                    })
                    .ok_or_else(|| {
                        BackendError::new(
                            "record field read without a row slot".into(),
                            expr.span,
                        )
                    })?;
                let src = self.compile_expr(receiver)?;
                let dest = self.fresh_local();
                self.push(Inst::TupleGet {
                    dest,
                    src,
                    index: u16::try_from(index).unwrap_or_default(),
                });
                Ok(Operand::Local(dest))
            }
            ExprKind::Variable(Name::Resolved(symbol, name)) => {
                if let Some(local) = self.locals.get(symbol).copied() {
                    // Last-use liveness: this read spends one use.
                    if let Some(count) = self.use_counts.get_mut(symbol)
                        && *count > 0
                    {
                        *count -= 1;
                    }
                    if self.moved.contains(&local) {
                        return Err(BackendError::new(
                            format!("use of moved value `{name}`"),
                            expr.span,
                        ));
                    }
                    if self.invalidated_views.contains(&local) {
                        return Err(BackendError::new(
                            format!("use of borrowed value `{name}` after its owner moved"),
                            expr.span,
                        ));
                    }
                    if let Some(loan) = self.live_loan_of(local, true) {
                        return Err(BackendError::new(
                            format!(
                                "`{name}` is already mutable borrowed as `{}`",
                                loan.view_name
                            ),
                            expr.span,
                        ));
                    }
                    if self.cell_handles.contains(&local) {
                        let dest = self.fresh_local();
                        self.push(Inst::CellGet {
                            dest,
                            cell: Operand::Local(local),
                        });
                        return Ok(Operand::Local(dest));
                    }
                    if self.owned_tys.contains_key(&local) {
                        self.record_flow(verify::FlowEvent::Use(local));
                    }
                    Ok(Operand::Local(local))
                } else if let Some(slot) = self.program_builder.global_slots.get(symbol).copied() {
                    if self.moved_globals.contains(&slot) {
                        return Err(BackendError::new(
                            format!("use of moved value `{name}`"),
                            expr.span,
                        ));
                    }
                    let dest = self.fresh_local();
                    self.push(Inst::GlobalLoad { dest, global: slot });
                    self.global_loads.insert(dest, slot);
                    Ok(Operand::Local(dest))
                } else if let Some(value) = self.subst.get(symbol).or_else(|| {
                    self.subst.get(&canonical(
                        *symbol,
                        self.program_builder.programs[self.program].module,
                    ))
                }) {
                    // ADR 0035 §6: a static parameter used as an ordinary
                    // value; this instance's substitution carries the
                    // concrete value, so specialization substitutes it.
                    match value {
                        Ty::Static(StaticValue::Int(int)) => match int
                            .as_constant()
                            .and_then(|constant| i64::try_from(constant).ok())
                        {
                            Some(constant) => Ok(Operand::Const(Constant::Int(constant))),
                            None => Err(BackendError::new(
                                format!("static parameter `{name}` has no concrete 64-bit value"),
                                expr.span,
                            )),
                        },
                        Ty::Static(StaticValue::Bool(value)) => {
                            Ok(Operand::Const(Constant::Bool(*value)))
                        }
                        Ty::Static(StaticValue::Case(_, variant)) => {
                            let module = self.program_builder.programs[self.program].module;
                            let Some((enum_symbol, tag)) = self
                                .program_builder
                                .variant_tag(canonical(*variant, module))
                            else {
                                return Err(BackendError::new(
                                    format!(
                                        "static parameter `{name}` names a variant without a known enum"
                                    ),
                                    expr.span,
                                ));
                            };
                            let dest = self.fresh_local();
                            self.push(Inst::Variant {
                                dest,
                                enum_symbol,
                                tag,
                                args: Vec::new(),
                            });
                            Ok(Operand::Local(dest))
                        }
                        // A rigid instance (TALK_CHECK_ALL compiles every
                        // callable generically; rigid demands stay rigid
                        // through nested calls and are never reached from
                        // the monomorphic entry). The static value is
                        // abstract here; every static domain is a Copy
                        // scalar, so a domain-shaped placeholder exercises
                        // the ownership pass exactly as a concrete value
                        // would.
                        Ty::Param(rigid) => {
                            match self.program_builder.static_param_domain(*rigid) {
                                Some(Ty::Nominal(symbol, _)) if symbol == Symbol::Int => {
                                    Ok(Operand::Const(Constant::Int(0)))
                                }
                                Some(Ty::Nominal(symbol, _)) if symbol == Symbol::Bool => {
                                    Ok(Operand::Const(Constant::Bool(false)))
                                }
                                Some(Ty::Nominal(enum_symbol, _)) => {
                                    let dest = self.fresh_local();
                                    self.push(Inst::Variant {
                                        dest,
                                        enum_symbol,
                                        tag: 0,
                                        args: Vec::new(),
                                    });
                                    Ok(Operand::Local(dest))
                                }
                                _ => Err(BackendError::new(
                                    format!(
                                        "static parameter `{name}` has no concrete value at this use"
                                    ),
                                    expr.span,
                                )),
                            }
                        }
                        _ => Err(BackendError::new(
                            format!("static parameter `{name}` has no concrete value at this use"),
                            expr.span,
                        )),
                    }
                } else if self.program_builder.callables.contains_key(&canonical(
                    *symbol,
                    self.program_builder.programs[self.program].module,
                )) {
                    // A named function used as a value: a captureless
                    // function value, specialized against the use site's
                    // recorded instantiation (the value's type pinned any
                    // generic and static arguments the frontend solved).
                    let target =
                        canonical(*symbol, self.program_builder.programs[self.program].module);
                    let mut subst: Vec<(Symbol, Ty)> = Vec::new();
                    if let Some(instantiation) = &expr.instantiation {
                        for (param, ty) in instantiation {
                            subst.push((*param, self.resolved(ty)));
                        }
                    }
                    // ADR 0035: a static parameter the use site leaves
                    // unpinned has no value for the body to read — there
                    // is no generic clause to fall back on.
                    if let Some(callable) = self.program_builder.callables.get(&target) {
                        for param in callable.body.scheme_params() {
                            let is_static = matches!(param.kind, ParamKind::Static(_));
                            // A leftover inference hole degrades to
                            // `Ty::Error` at finalization; neither form
                            // pins a value the body could read.
                            let pinned = subst.iter().any(|(symbol, ty)| {
                                *symbol == param.symbol && !matches!(ty, Ty::Var(_) | Ty::Error)
                            });
                            if is_static && !pinned {
                                return Err(BackendError::new(
                                    format!(
                                        "`{name}` has static parameters this use does not fix; call it directly, or use it where its type pins every static argument"
                                    ),
                                    expr.span,
                                ));
                            }
                        }
                    }
                    let func = self.demand_specialized(target, subst, expr.span)?;
                    let dest = self.fresh_local();
                    self.push(Inst::MakeClosure {
                        dest,
                        func,
                        env: Vec::new(),
                    });
                    Ok(Operand::Local(dest))
                } else if let Some((initializer, _)) = self
                    .program_builder
                    .globals
                    .get(&canonical(
                        *symbol,
                        self.program_builder.programs[self.program].module,
                    ))
                    .copied()
                {
                    // Only literal global initializers inline; anything
                    // needing real once-only storage stays rejected.
                    match &initializer.kind {
                        ExprKind::Lit(Literal::Int(_) | Literal::Float(_) | Literal::Bool(_)) => {
                            let owner = self.program_builder.globals[&canonical(
                                *symbol,
                                self.program_builder.programs[self.program].module,
                            )]
                                .1;
                            let previous = self.program;
                            self.program = owner;
                            let value = self.compile_expr(initializer);
                            self.program = previous;
                            value
                        }
                        _ => Err(BackendError::unsupported(
                            "global values without literal initializers are not supported yet"
                                .into(),
                            expr.span,
                        )),
                    }
                } else {
                    Err(BackendError::unsupported(
                        "function and global values are not supported yet".into(),
                        expr.span,
                    ))
                }
            }
            ExprKind::Block(block) | ExprKind::Unsafe(block) => self.compile_block(block),
            ExprKind::Match(scrutinee, arms) => {
                let value = self.compile_expr(scrutinee)?;
                let scrutinee_ty = self.resolved(&scrutinee.ty);
                // Destructuring an owned scrutinee IS its consumption
                // (CHG-07's whole-aggregate rule, and the checker's
                // clone-before-reuse model): binds take payload ownership
                // and each arm releases the payloads it leaves unbound.
                // Borrowed scrutinees (untracked place reads) keep alias
                // semantics.
                let owning = self.consume_operand(value);
                let result = self.compile_match(value, &scrutinee_ty, arms, owning)?;
                if let Operand::Local(local) = result {
                    self.produce_temp(local, &ty);
                }
                Ok(result)
            }
            ExprKind::Call { callee, args, .. } => self.compile_call(expr, callee, args),
            ExprKind::InlineIR(instruction) => self.compile_inline_ir(expr, instruction),
            ExprKind::LiteralArray(items) => {
                // `[a, b, c]`: allocate the buffer, store each element,
                // wrap it in the core Array layout {storage, count,
                // capacity} (the same shape `Array.init` builds).
                let Ty::Nominal(array_symbol, type_args) = &ty else {
                    return Err(BackendError::new(
                        "array literal without an Array type".into(),
                        expr.span,
                    ));
                };
                if *array_symbol == Symbol::InlineArray {
                    let [element_ty, count_ty] = type_args.as_slice() else {
                        return Err(BackendError::new(
                            "InlineArray literal has malformed type arguments".into(),
                            expr.span,
                        ));
                    };
                    let count = match count_ty {
                        Ty::Static(StaticValue::Int(count)) => count.as_i64(),
                        _ => None,
                    };
                    if count != i64::try_from(items.len()).ok() {
                        return Err(BackendError::new(
                            "InlineArray literal length does not match its type".into(),
                            expr.span,
                        ));
                    }
                    if items.len() > usize::from(u16::MAX) {
                        return Err(BackendError::new(
                            "InlineArray exceeds the backend element limit".into(),
                            expr.span,
                        ));
                    }
                    let mut values = Vec::with_capacity(items.len());
                    for item in items {
                        let value = self.compile_expr(item)?;
                        self.consume_binding(value, element_ty, item.span)?;
                        values.push(value);
                    }
                    let dest = self.fresh_local();
                    self.push(Inst::Record {
                        dest,
                        struct_symbol: Symbol::InlineArray,
                        args: values,
                    });
                    self.produce_temp(dest, &ty);
                    return Ok(Operand::Local(dest));
                }
                if *array_symbol != Symbol::Array {
                    return Err(BackendError::new(
                        "array literal without an Array or InlineArray type".into(),
                        expr.span,
                    ));
                }
                // Raw storage buffers hold values the region walk never
                // scans: `'heap` handles cannot live in them.
                if type_args
                    .iter()
                    .any(|arg| contains_object(self.program_builder, arg))
                {
                    return Err(BackendError::new(
                        "a `'heap` value cannot be stored in raw storage (Array elements are unscanned)"
                            .into(),
                        expr.span,
                    ));
                }
                let array_symbol = canonical(
                    *array_symbol,
                    self.program_builder.programs[self.program].module,
                );
                let element_ty = type_args.first().cloned().unwrap_or(Ty::Error);
                let element = mem_ty_of(&element_ty);
                let count = i64::try_from(items.len()).unwrap_or_default();

                let base = self.fresh_local();
                self.push(Inst::Alloc {
                    dest: base,
                    bytes: Operand::Const(Constant::Int(count * i64::from(element.size()))),
                });
                for (index, item) in items.iter().enumerate() {
                    let value = self.compile_expr(item)?;
                    self.consume_binding(value, &element_ty, item.span)?;
                    let slot = self.fresh_local();
                    self.push(Inst::PtrAdd {
                        dest: slot,
                        ptr: Operand::Local(base),
                        offset: Operand::Const(Constant::Int(
                            i64::try_from(index).unwrap_or_default(),
                        )),
                        size: element.size(),
                    });
                    self.push(Inst::Store {
                        ptr: Operand::Local(slot),
                        src: value,
                        kind: element,
                    });
                }
                let storage = self.fresh_local();
                self.push(Inst::Record {
                    dest: storage,
                    struct_symbol: Symbol::Storage,
                    args: vec![Operand::Local(base)],
                });
                let dest = self.fresh_local();
                self.push(Inst::Record {
                    dest,
                    struct_symbol: array_symbol,
                    args: vec![
                        Operand::Local(storage),
                        Operand::Const(Constant::Int(count)),
                        Operand::Const(Constant::Int(count)),
                    ],
                });
                self.produce_temp(dest, &ty);
                Ok(Operand::Local(dest))
            }
            ExprKind::Func(func) => self.compile_closure(func, &expr.ty),
            ExprKind::Clone(source) => {
                // Typing selected the clone (CHG-09): Copy duplicates the
                // value; CheapClone adds one reference per owned buffer
                // (copy-on-write's O(1) clone).
                let value = self.compile_expr(source)?;
                let source_ty = self.resolved(&source.ty);
                if is_linear(self.program_builder, &source_ty) {
                    return Err(BackendError::new(
                        "the `copy` marker requires a Copy or CheapClone value (linear values are never cloneable)"
                            .into(),
                        expr.span,
                    ));
                }
                let dest = self.fresh_local();
                self.push(Inst::Copy { dest, src: value });
                if contains_buffer(self.program_builder, &source_ty) {
                    let mut retained = source_ty.clone();
                    while let Ty::Borrow(_, inner) = retained {
                        retained = *inner;
                    }
                    self.retain_value(Operand::Local(dest), &retained, expr.span)?;
                }
                self.produce_temp(dest, &ty);
                Ok(Operand::Local(dest))
            }
            ExprKind::CallEffect {
                effect_name, args, ..
            } => {
                let Name::Resolved(effect, _) = effect_name else {
                    return Err(BackendError::new(
                        "perform without a resolved effect".into(),
                        expr.span,
                    ));
                };
                let effect = canonical(*effect, self.program_builder.programs[self.program].module);
                // The runtime is the implicit handler for the core `'io`
                // effect: a perform dispatches on the request's tag
                // straight to the host operation (IO-02). User handlers
                // for ambient effects stay out of scope for v1.
                if self.program_builder.is_io_effect(effect) {
                    return self.compile_io_perform(expr, args);
                }
                // One clause body serves every instantiation over rigid
                // payload types: payloads travel in native layout and the
                // perform site appends one `[drop, retain]` witness pair
                // per effect generic — value-witness-table passing (the
                // model of Swift's unspecialized-generics ABI and Go's
                // generics dictionaries, Griesemer et al. OOPSLA 2022;
                // dictionary passing per Wadler & Blott, POPL 1989).
                let (declared_params, sig_generics, sig_module) =
                    match self.program_builder.effect_sig(effect) {
                        Some((sig, sig_module)) => (
                            sig.params
                                .iter()
                                .map(|param| canonical_ty(param, sig_module))
                                .collect::<Vec<_>>(),
                            // Witness blocks travel per TYPE generic;
                            // static value generics have no payload
                            // values to drop or retain.
                            type_param_symbols(&sig.generics),
                            sig_module,
                        ),
                        None => (
                            Vec::new(),
                            Vec::new(),
                            self.program_builder.programs[self.program].module,
                        ),
                    };
                let mut operands = Vec::new();
                let mut payload_tys = Vec::new();
                let mut mut_arg_places: Vec<(usize, PlaceChain)> = Vec::new();
                for arg in args {
                    let payload_ty = self.resolved(&arg.value.ty);
                    if matches!(arg.mode, Some(ArgMode::Mut)) {
                        // The clause resumes with the evolved value; it
                        // writes back into the argument's place.
                        let Some(chain) = self.resolve_place(&arg.value)? else {
                            return Err(BackendError::unsupported(
                                "a `mut` argument that does not name a place is not supported yet"
                                    .into(),
                                arg.value.span,
                            ));
                        };
                        mut_arg_places.push((operands.len(), chain));
                    }
                    let operand = self.compile_expr(&arg.value)?;
                    // Effect arguments transfer to the clause.
                    self.consume_binding(operand, &payload_ty, arg.value.span)?;
                    payload_tys.push(payload_ty);
                    operands.push(operand);
                }
                // Writeback targets align against the declared parameters
                // before the witness blocks are appended.
                let declared_fn = Ty::Func(
                    declared_params.clone(),
                    Box::new(Ty::Error),
                    crate::types::ty::EffectRow {
                        effects: Vec::new(),
                        tail: None,
                    },
                );
                let targets = self.writeback_targets(
                    &declared_fn,
                    operands.len(),
                    None,
                    &mut_arg_places,
                    args,
                    0,
                )?;
                // Resolve each generic to this perform's concrete type:
                // the checker's recorded instantiation first, else
                // structurally from the argument types.
                let mut instantiation: Vec<(Symbol, Ty)> = Vec::new();
                if let Some(recorded) = &expr.instantiation {
                    for (param, arg_ty) in recorded {
                        instantiation.push((*param, self.resolved(arg_ty)));
                    }
                }
                for generic in &sig_generics {
                    // Rigid params keep their authored identity; recorded
                    // instantiation keys may carry either the raw or the
                    // owner-stamped form.
                    let mut solved = instantiation
                        .iter()
                        .find(|(param, _)| {
                            param == generic || *param == canonical(*generic, sig_module)
                        })
                        .map(|(_, arg_ty)| arg_ty.clone());
                    if solved.is_none() {
                        for (declared, payload_ty) in declared_params.iter().zip(&payload_tys) {
                            solved = solve_param(declared, payload_ty, *generic);
                            if solved.is_some() {
                                break;
                            }
                        }
                    }
                    let Some(solved) = solved else {
                        return Err(BackendError::unsupported(
                            "a generic effect instantiation the backend cannot resolve is not supported yet"
                                .into(),
                            expr.span,
                        ));
                    };
                    if let Ty::Param(rigid) = &solved {
                        // A re-perform from inside a clause forwards its
                        // own witnesses for the still-rigid generic. The
                        // target generic's constraints are a subset of the
                        // rigid one's (typing proved the perform), so its
                        // dictionaries forward from the same frame.
                        let rigid = self.canon_rigid(*rigid);
                        let Some((drop_witness, retain_witness)) =
                            self.param_witnesses.get(&rigid).copied()
                        else {
                            return Err(BackendError::unsupported(
                                "a generic value cannot cross this boundary without its ownership witnesses (not supported yet)"
                                    .into(),
                                expr.span,
                            ));
                        };
                        operands.push(Operand::Local(drop_witness));
                        operands.push(Operand::Local(retain_witness));
                        for protocol in self.program_builder.rigid_constraints(*generic) {
                            let Some(locals) = self
                                .param_requirements
                                .get(&(rigid, protocol.protocol))
                                .cloned()
                            else {
                                return Err(BackendError::unsupported(
                                    "a generic value cannot cross this boundary without its conformance dictionaries (not supported yet)"
                                        .into(),
                                    expr.span,
                                ));
                            };
                            operands.extend(locals.into_iter().map(Operand::Local));
                        }
                    } else {
                        // Concrete or compound: glue closures capture any
                        // inner rigid witnesses they need; requirement
                        // closures select implementations like a static
                        // call would.
                        let drop_witness = self.glue_closure(&solved, Glue::Drop, expr.span)?;
                        let retain_witness = self.glue_closure(&solved, Glue::Retain, expr.span)?;
                        operands.push(drop_witness);
                        operands.push(retain_witness);
                        for protocol in self.program_builder.rigid_constraints(*generic) {
                            let requirements = self
                                .program_builder
                                .protocol_requirements(protocol.protocol)
                                .unwrap_or_default();
                            for name in requirements {
                                let closure =
                                    self.requirement_closure(&solved, &protocol, &name, expr.span)?;
                                operands.push(closure);
                            }
                        }
                    }
                }
                // Route through the capability in scope at this perform's
                // lexical position: the captured creation-site handler
                // when this frame carries one, dynamic nearest-handler
                // search otherwise. Either way the clause runs outside its
                // own handler (CHG-01): the search floor is the handler's
                // index for the clause call's extent.
                let (clause, index) = self.capability(effect);
                let saved_floor = self.fresh_local();
                self.push(Inst::GetFloor { dest: saved_floor });
                self.push(Inst::SetFloor {
                    src: Operand::Local(index),
                });
                let dest = self.fresh_local();
                let unwind = None;
                self.push(Inst::CallIndirect {
                    dest,
                    callee: Operand::Local(clause),
                    args: operands,
                    unwind,
                });
                self.push(Inst::SetFloor {
                    src: Operand::Local(saved_floor),
                });
                self.apply_writebacks(dest, targets, &ty, expr.span)
            }
            _ => Err(BackendError::unsupported(
                "this expression is not supported yet".into(),
                expr.span,
            )),
        }
    }

    fn compile_literal(&mut self, expr: &Expr, literal: &Literal) -> Result<Operand, BackendError> {
        match literal {
            Literal::Int(text) => match self.types().integer_literals.get(&expr.id) {
                Some(CheckedIntegerLiteral::Value(value)) => {
                    Ok(Operand::Const(Constant::Int(*value)))
                }
                Some(CheckedIntegerLiteral::Invalid) => Err(BackendError::new(
                    "integer literal without a checked 64-bit value".into(),
                    expr.span,
                )),
                // Builder-synthesized nodes (cloned receivers, elaborated
                // loops) carry fresh ids; their text already passed LIT-01
                // checking under the original node.
                None => text
                    .replace('_', "")
                    .parse()
                    .map(Constant::Int)
                    .map(Operand::Const)
                    .map_err(|_| {
                        BackendError::new(
                            "integer literal without a checked 64-bit value".into(),
                            expr.span,
                        )
                    }),
            },
            Literal::Float(text) => {
                let value: f64 = text
                    .replace('_', "")
                    .parse()
                    .map_err(|_| BackendError::new("invalid float literal".into(), expr.span))?;
                Ok(Operand::Const(Constant::Float(value)))
            }
            Literal::Bool(value) => Ok(Operand::Const(Constant::Bool(*value))),
            Literal::String(text) => {
                let text = crate::parsing::lexing::unescape(text)
                    .map_err(|_| BackendError::new("invalid string escape".into(), expr.span))?;
                let dest = self.fresh_local();
                self.push(Inst::StringLit {
                    dest,
                    bytes: text.into_bytes(),
                });
                Ok(Operand::Local(dest))
            }
            Literal::Character(text) => {
                // A character literal is a borrowed grapheme view over
                // immortal static bytes: Character { storage, start,
                // byte_count } (layout owned by core/Unicode.tlk).
                let text = crate::parsing::lexing::unescape(text)
                    .map_err(|_| BackendError::new("invalid character escape".into(), expr.span))?;
                let bytes = text.into_bytes();
                let len = i64::try_from(bytes.len()).unwrap_or_default();
                let ptr = self.fresh_local();
                self.push(Inst::BytesLit { dest: ptr, bytes });
                let storage = self.fresh_local();
                self.push(Inst::Record {
                    dest: storage,
                    struct_symbol: Symbol::Storage,
                    args: vec![Operand::Local(ptr)],
                });
                let dest = self.fresh_local();
                self.push(Inst::Record {
                    dest,
                    struct_symbol: Symbol::Character,
                    args: vec![
                        Operand::Local(storage),
                        Operand::Const(Constant::Int(0)),
                        Operand::Const(Constant::Int(len)),
                    ],
                });
                Ok(Operand::Local(dest))
            }
        }
    }

    /// Sequential pattern tests over a scalar scrutinee: each refutable arm
    /// branches to the next test on failure.
    fn compile_match(
        &mut self,
        scrutinee: Operand,
        scrutinee_ty: &Ty,
        arms: &[crate::typed_ast::MatchArm],
        owning: bool,
    ) -> Result<Operand, BackendError> {
        let result = self.fresh_local();
        let join = self.new_block();

        // One tag read serves every arm of this match; a nested match
        // (in an arm body) scopes its own cache, restored below.
        let outer_tag_cache = std::mem::take(&mut self.match_tag_cache);

        let moved_before = self.moved.clone();
        let globals_before = self.moved_globals.clone();
        let temps_before = self.stmt_temps.clone();
        let mut arm_ends: Vec<ArmEnd> = Vec::new();
        for arm in arms {
            let matched = self.new_block();
            let next_test = self.new_block();
            self.compile_pattern_test(&arm.pattern, scrutinee, scrutinee_ty, matched, next_test)?;

            self.switch_to(matched);
            self.moved = moved_before.clone();
            self.moved_globals = globals_before.clone();
            self.stmt_temps = temps_before.clone();
            if owning {
                // The matched arm settles the consumed scrutinee: binds
                // become arm-owned temporaries (the merge machinery drops
                // the unconsumed ones path-sensitively) and unbound owned
                // payloads release here, re-extracted from the intact
                // scrutinee register.
                self.settle_owned_match(&arm.pattern, scrutinee, scrutinee_ty, false)?;
            }
            let value = self.compile_block(&arm.body)?;
            if !self.terminated() {
                arm_ends.push(ArmEnd {
                    block: self.current,
                    value,
                    moved: std::mem::take(&mut self.moved),
                    moved_globals: std::mem::take(&mut self.moved_globals),
                    temps: std::mem::take(&mut self.stmt_temps),
                });
            }

            self.switch_to(next_test);
            // (pattern tests were compiled in the pre-arm block)
        }
        // The frontend checks exhaustiveness; a fall-through here is a
        // backend bug surfaced as a deterministic trap, not undefined
        // behavior.
        self.terminate(Term::Trap("unmatched value"));

        self.merge_arms(arm_ends, result, join, temps_before, moved_before);
        self.match_tag_cache = outer_tag_cache;
        Ok(Operand::Local(result))
    }

    /// Settle a consumed scrutinee for one matched arm: register each
    /// bind as an arm-owned temporary, and release unbound owned payloads
    /// by re-extracting them from the scrutinee register (which every
    /// path to the matched block has assigned).
    fn settle_owned_match(
        &mut self,
        pattern: &Pattern,
        scrutinee: Operand,
        scrutinee_ty: &Ty,
        through_borrow: bool,
    ) -> Result<(), BackendError> {
        let ty = strip_borrows(self.resolved(scrutinee_ty));
        match &pattern.kind {
            PatternKind::Bind(Name::Resolved(symbol, _)) => {
                if let Some(local) = self.locals.get(symbol).copied()
                    && self.needs_release(&ty)
                {
                    // A bind reached through a borrow-typed layer shares
                    // the view's interior: the arm owns the binding (it
                    // drops below), so it donates a reference on the way
                    // in (rule 1 of docs/ownership-rethink-plan.md).
                    // Without the retain the arm's drop releases the
                    // lender's reference — the tuple-match double free.
                    if through_borrow {
                        self.retain_value(Operand::Local(local), &ty, pattern.span)?;
                    }
                    self.produce_temp(local, &ty);
                }
                Ok(())
            }
            PatternKind::Wildcard
            | PatternKind::LiteralInt(_)
            | PatternKind::LiteralString(_)
            | PatternKind::LiteralCharacter(_)
            | PatternKind::LiteralTrue
            | PatternKind::LiteralFalse => {
                // A view's interior is the lender's to release, not the
                // arm's.
                if !through_borrow && self.needs_release(&ty) {
                    self.drop_value(scrutinee, &ty);
                }
                Ok(())
            }
            PatternKind::Tuple(elements) => {
                let element_tys = tuple_element_tys(&ty, elements.len());
                for (index, (element, element_ty)) in elements.iter().zip(&element_tys).enumerate()
                {
                    if pattern_bind_symbols(element).is_empty() && !self.needs_release(element_ty) {
                        continue;
                    }
                    let extracted = self.fresh_local();
                    self.push(Inst::TupleGet {
                        dest: extracted,
                        src: scrutinee,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    self.settle_owned_match(
                        element,
                        Operand::Local(extracted),
                        element_ty,
                        through_borrow,
                    )?;
                }
                Ok(())
            }
            PatternKind::Variant {
                variant_name,
                fields,
                ..
            } => {
                let Some((_, _, payload_tys)) =
                    self.variant_case(pattern, variant_name, &ty, fields.len())
                else {
                    return Ok(());
                };
                for (index, (field, payload_ty)) in fields.iter().zip(&payload_tys).enumerate() {
                    if pattern_bind_symbols(field).is_empty() && !self.needs_release(payload_ty) {
                        continue;
                    }
                    let extracted = self.fresh_local();
                    self.push(Inst::GetPayload {
                        dest: extracted,
                        src: scrutinee,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    self.settle_owned_match(
                        field,
                        Operand::Local(extracted),
                        payload_ty,
                        through_borrow,
                    )?;
                }
                Ok(())
            }
            PatternKind::Or(alternatives) => {
                // Alternatives share their binds; unbound owned payloads
                // would need to know which alternative matched.
                let any_unbound_owned = alternatives
                    .iter()
                    .any(|alternative| self.pattern_leaves_owned_unbound(alternative, &ty));
                if any_unbound_owned {
                    return Err(BackendError::unsupported(
                        "or-patterns that leave owned payloads unbound on a consumed value are not supported yet"
                            .into(),
                        pattern.span,
                    ));
                }
                if let Some(first) = alternatives.first() {
                    self.settle_owned_match(first, scrutinee, &ty, through_borrow)?;
                }
                Ok(())
            }
            PatternKind::Record { fields } => {
                let cells = self.record_cells(pattern, fields, &ty)?;
                for (index, cell) in cells.iter().enumerate() {
                    if let Some(name) = &cell.bind {
                        // The label binder owns the slot; interior binds
                        // of the same owned value would make two owners.
                        if self.needs_release(&cell.field_ty) {
                            if !pattern_bind_symbols(&cell.pattern).is_empty() {
                                return Err(BackendError::unsupported(
                                    "record patterns that bind both a field and its interior on a consumed value are not supported yet"
                                        .into(),
                                    pattern.span,
                                ));
                            }
                            if let Some(local) = name
                                .symbol()
                                .ok()
                                .and_then(|s| self.locals.get(&s).copied())
                            {
                                if through_borrow {
                                    self.retain_value(
                                        Operand::Local(local),
                                        &cell.field_ty,
                                        pattern.span,
                                    )?;
                                }
                                self.produce_temp(local, &cell.field_ty);
                            }
                        }
                        continue;
                    }
                    if pattern_bind_symbols(&cell.pattern).is_empty()
                        && !self.needs_release(&cell.field_ty)
                    {
                        continue;
                    }
                    let extracted = self.fresh_local();
                    self.push(Inst::TupleGet {
                        dest: extracted,
                        src: scrutinee,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    self.settle_owned_match(
                        &cell.pattern,
                        Operand::Local(extracted),
                        &cell.field_ty,
                        through_borrow,
                    )?;
                }
                Ok(())
            }
            PatternKind::Struct {
                fields,
                field_names,
                ..
            } => {
                let (heap, cells) = self.struct_cells(pattern, fields, field_names, &ty)?;
                for (index, cell) in cells.iter().enumerate() {
                    if pattern_bind_symbols(&cell.pattern).is_empty()
                        && !self.needs_release(&cell.field_ty)
                    {
                        continue;
                    }
                    // A heap object's drop releases its stored fields, so
                    // its projections settle exactly like fields reached
                    // through a borrow: binds donate, unbound stays the
                    // object's.
                    if heap && matches!(cell.pattern.kind, PatternKind::Wildcard) {
                        continue;
                    }
                    let extracted = self.fresh_local();
                    if heap {
                        self.push(Inst::ObjectGet {
                            dest: extracted,
                            src: scrutinee,
                            index: u16::try_from(index).unwrap_or_default(),
                        });
                    } else {
                        self.push(Inst::GetField {
                            dest: extracted,
                            src: scrutinee,
                            index: u16::try_from(index).unwrap_or_default(),
                        });
                    }
                    self.settle_owned_match(
                        &cell.pattern,
                        Operand::Local(extracted),
                        &cell.field_ty,
                        through_borrow || heap,
                    )?;
                }
                if heap && !through_borrow && self.needs_release(&ty) {
                    self.drop_value(scrutinee, &ty);
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Whether matching this pattern against a consumed value of `ty`
    /// would leave any owned payload without a binding.
    fn pattern_leaves_owned_unbound(&self, pattern: &Pattern, ty: &Ty) -> bool {
        match &pattern.kind {
            PatternKind::Bind(_) => false,
            PatternKind::Tuple(elements) => match ty {
                Ty::Tuple(items) => elements
                    .iter()
                    .zip(items)
                    .any(|(element, item)| self.pattern_leaves_owned_unbound(element, item)),
                _ => false,
            },
            PatternKind::Record { fields } => match self.record_cells(pattern, fields, ty) {
                Ok(cells) => cells.iter().any(|cell| {
                    cell.bind.is_none()
                        && self.pattern_leaves_owned_unbound(&cell.pattern, &cell.field_ty)
                }),
                Err(_) => self.needs_release(ty),
            },
            PatternKind::Variant {
                variant_name,
                fields,
                ..
            } => match self.variant_case(pattern, variant_name, ty, fields.len()) {
                Some((_, _, payload_tys)) => {
                    fields.iter().zip(&payload_tys).any(|(field, payload_ty)| {
                        self.pattern_leaves_owned_unbound(field, payload_ty)
                    })
                }
                None => self.needs_release(ty),
            },
            PatternKind::Or(alternatives) => alternatives
                .iter()
                .any(|alternative| self.pattern_leaves_owned_unbound(alternative, ty)),
            PatternKind::Struct {
                fields,
                field_names,
                ..
            } => match self.struct_cells(pattern, fields, field_names, ty) {
                // A heap object's unbound fields stay the object's; its
                // own drop releases them, so nothing is left unowned.
                Ok((true, _)) => false,
                Ok((false, cells)) => cells
                    .iter()
                    .any(|cell| self.pattern_leaves_owned_unbound(&cell.pattern, &cell.field_ty)),
                Err(_) => self.needs_release(ty),
            },
            _ => self.needs_release(ty),
        }
    }

    /// Expand a record pattern against the scrutinee's resolved row:
    /// one cell per row slot in layout order. This is the single owner
    /// of the name-to-slot rule; every pattern site delegates here and
    /// then reuses the positional (tuple) machinery.
    fn record_cells(
        &self,
        pattern: &Pattern,
        fields: &[RecordFieldPattern],
        scrutinee_ty: &Ty,
    ) -> Result<Vec<RecordCell>, BackendError> {
        let Ty::Record(row) = strip_borrows(self.resolved(scrutinee_ty)) else {
            return Err(BackendError::new(
                "record pattern on a non-record scrutinee".into(),
                pattern.span,
            ));
        };
        if row.tail.is_some() {
            // Slot positions depend on the whole row; an open row has
            // no fixed layout to match against (the reference lowering
            // rejected these too).
            return Err(BackendError::unsupported(
                "record patterns on open rows are not supported yet".into(),
                pattern.span,
            ));
        }
        row.fields
            .iter()
            .map(|(label, field_ty)| {
                let crate::label::Label::Named(label) = label else {
                    return Err(BackendError::new(
                        "record pattern on a row with positional fields".into(),
                        pattern.span,
                    ));
                };
                let cell = fields.iter().find_map(|field| match &field.kind {
                    RecordFieldPatternKind::Bind(name) if name.name_str() == *label => {
                        Some(RecordCell {
                            field_ty: field_ty.clone(),
                            pattern: Pattern {
                                id: field.id,
                                kind: PatternKind::Bind(name.clone()),
                                span: pattern.span,
                            },
                            bind: None,
                        })
                    }
                    RecordFieldPatternKind::Equals { name, value } if name.name_str() == *label => {
                        // `label: _` is the label binder alone.
                        if matches!(value.kind, PatternKind::Wildcard) {
                            Some(RecordCell {
                                field_ty: field_ty.clone(),
                                pattern: Pattern {
                                    id: field.id,
                                    kind: PatternKind::Bind(name.clone()),
                                    span: pattern.span,
                                },
                                bind: None,
                            })
                        } else {
                            Some(RecordCell {
                                field_ty: field_ty.clone(),
                                pattern: value.clone(),
                                bind: Some(name.clone()),
                            })
                        }
                    }
                    _ => None,
                });
                Ok(cell.unwrap_or_else(|| RecordCell {
                    field_ty: field_ty.clone(),
                    pattern: Pattern {
                        id: pattern.id,
                        kind: PatternKind::Wildcard,
                        span: pattern.span,
                    },
                    bind: None,
                }))
            })
            .collect()
    }

    /// One cell per stored field of the struct, in declaration order —
    /// the struct analog of `record_cells`. Fields the pattern leaves to
    /// `..` become wildcards. Returns the (canonical symbol, heap flag)
    /// alongside the cells; heap structs project fields as views of the
    /// object rather than owned slots.
    fn struct_cells(
        &self,
        pattern: &Pattern,
        fields: &[Pattern],
        field_names: &[Name],
        scrutinee_ty: &Ty,
    ) -> Result<(bool, Vec<RecordCell>), BackendError> {
        let Ty::Nominal(symbol, args) = strip_borrows(self.resolved(scrutinee_ty)) else {
            return Err(BackendError::new(
                "struct pattern on a non-struct scrutinee".into(),
                pattern.span,
            ));
        };
        let symbol = canonical(symbol, self.program_builder.programs[self.program].module);
        let Some((def, _)) = self.program_builder.struct_def(symbol) else {
            return Err(BackendError::new(
                "struct pattern without a struct definition".into(),
                pattern.span,
            ));
        };
        let heap = def.heap;
        let names: Vec<String> = def.fields.keys().cloned().collect();
        let Some(field_tys) = self.program_builder.field_types(symbol, &args) else {
            return Err(BackendError::new(
                "struct pattern without field types".into(),
                pattern.span,
            ));
        };
        let cells = names
            .iter()
            .zip(field_tys)
            .map(|(name, field_ty)| {
                let sub = field_names
                    .iter()
                    .zip(fields)
                    .find(|(label, _)| label.name_str() == *name)
                    .map(|(_, sub)| sub.clone());
                RecordCell {
                    field_ty,
                    pattern: sub.unwrap_or(Pattern {
                        id: pattern.id,
                        kind: PatternKind::Wildcard,
                        span: pattern.span,
                    }),
                    bind: None,
                }
            })
            .collect();
        Ok((heap, cells))
    }

    /// Project every stored field of a struct value, `GetField` for value
    /// structs and `ObjectGet` for heap structs (whose results are views
    /// of the object, not owned slots).
    fn extract_struct_fields(&mut self, scrutinee: Operand, heap: bool, len: usize) -> Vec<Operand> {
        (0..len)
            .map(|index| {
                let dest = self.fresh_local();
                let index = u16::try_from(index).unwrap_or_default();
                if heap {
                    self.push(Inst::ObjectGet {
                        dest,
                        src: scrutinee,
                        index,
                    });
                } else {
                    self.push(Inst::GetField {
                        dest,
                        src: scrutinee,
                        index,
                    });
                }
                Operand::Local(dest)
            })
            .collect()
    }

    /// Demand a specialization, completing the substitution from this
    /// frame: a scheme parameter the recorded instantiation leaves
    /// unbound takes the enclosing instance's binding for the same
    /// parameter. Typing keeps recursive uses monomorphic (no recorded
    /// instantiation), so a recursive inferred generic specializes
    /// through the instance already being compiled — the static
    /// sub-dictionary rule (Griesemer et al., OOPSLA 2022).
    fn demand_specialized(
        &mut self,
        target: Symbol,
        mut subst: Vec<(Symbol, Ty)>,
        span: Span,
    ) -> Result<FuncId, BackendError> {
        if let Some(callable) = self.program_builder.callables.get(&target) {
            for param in callable.body.scheme_params() {
                if subst.iter().any(|(symbol, _)| *symbol == param.symbol) {
                    continue;
                }
                if let Some(ty) = self.subst.get(&param.symbol) {
                    subst.push((param.symbol, ty.clone()));
                }
            }
        }
        self.program_builder.demand(target, subst, span)
    }

    /// Resolve a variant pattern to its enum head, tag, and payload
    /// types: typing's resolution when present
    /// (`member_resolutions[pattern]`), the scrutinee's enum by name
    /// otherwise (elaboration-synthesized patterns carry fresh ids).
    fn variant_case(
        &self,
        pattern: &Pattern,
        variant_name: &str,
        scrutinee_ty: &Ty,
        payload_len: usize,
    ) -> Option<(Symbol, u16, Vec<Ty>)> {
        let module = self.program_builder.programs[self.program].module;
        let (head_from_ty, args) = match strip_borrows(self.resolved(scrutinee_ty)) {
            Ty::Nominal(head, args) => (Some(canonical(head, module)), args),
            _ => (None, Vec::new()),
        };
        let resolved = match self.types().member_resolutions.get(&pattern.id) {
            Some(crate::types::output::MemberResolution::Direct(variant)) => self
                .program_builder
                .variant_tag(canonical(*variant, module)),
            _ => head_from_ty.and_then(|head| {
                self.program_builder
                    .enum_def(head)
                    .and_then(|(def, _)| def.variants.get_index_of(variant_name))
                    .and_then(|tag| u16::try_from(tag).ok())
                    .map(|tag| (head, tag))
            }),
        };
        let (head, tag) = resolved?;
        let payload_tys = self
            .program_builder
            .variant_payloads(head, &args)
            .and_then(|payloads| payloads.get(usize::from(tag)).cloned())
            .unwrap_or_else(|| vec![Ty::Error; payload_len]);
        Some((head, tag, payload_tys))
    }

    fn compile_pattern_test(
        &mut self,
        pattern: &Pattern,
        scrutinee: Operand,
        scrutinee_ty: &Ty,
        matched: BlockId,
        failed: BlockId,
    ) -> Result<(), BackendError> {
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.terminate(Term::Goto(matched, Vec::new()));
                Ok(())
            }
            PatternKind::Bind(Name::Resolved(symbol, _)) => {
                let local = match self.locals.get(symbol) {
                    Some(local) => *local,
                    None => {
                        let local = self.fresh_local();
                        self.locals.insert(*symbol, local);
                        local
                    }
                };
                self.push(Inst::Copy {
                    dest: local,
                    src: scrutinee,
                });
                self.terminate(Term::Goto(matched, Vec::new()));
                Ok(())
            }
            PatternKind::LiteralTrue | PatternKind::LiteralFalse => {
                let expected = matches!(pattern.kind, PatternKind::LiteralTrue);
                self.branch_if_equal(
                    ScalarOp::BoolCmp(CmpKind::Eq),
                    scrutinee,
                    Operand::Const(Constant::Bool(expected)),
                    matched,
                    failed,
                );
                Ok(())
            }
            PatternKind::LiteralInt(_) => {
                let Some(CheckedIntegerLiteral::Value(value)) =
                    self.types().integer_literals.get(&pattern.id)
                else {
                    return Err(BackendError::new(
                        "integer pattern without a checked 64-bit value".into(),
                        pattern.span,
                    ));
                };
                self.branch_if_equal(
                    ScalarOp::IntCmp(CmpKind::Eq),
                    scrutinee,
                    Operand::Const(Constant::Int(*value)),
                    matched,
                    failed,
                );
                Ok(())
            }
            PatternKind::Tuple(elements) => {
                let element_tys = tuple_element_tys(scrutinee_ty, elements.len());
                let extracted = self.extract_tuple(scrutinee, elements.len());
                self.test_all(elements, &extracted, &element_tys, matched, failed)
            }
            PatternKind::Variant {
                variant_name,
                fields,
                ..
            } => {
                let Some((_, tag, payload_tys)) =
                    self.variant_case(pattern, variant_name, scrutinee_ty, fields.len())
                else {
                    return Err(BackendError::new(
                        "variant pattern without a frontend resolution".into(),
                        pattern.span,
                    ));
                };
                let tag_value = match scrutinee {
                    Operand::Local(local) => {
                        if let Some(&cached) = self.match_tag_cache.get(&local) {
                            cached
                        } else {
                            let tag_value = self.fresh_local();
                            self.push(Inst::GetTag {
                                dest: tag_value,
                                src: scrutinee,
                            });
                            self.match_tag_cache.insert(local, tag_value);
                            tag_value
                        }
                    }
                    Operand::Const(_) => {
                        let tag_value = self.fresh_local();
                        self.push(Inst::GetTag {
                            dest: tag_value,
                            src: scrutinee,
                        });
                        tag_value
                    }
                };
                let payloads = self.new_block();
                self.branch_if_equal(
                    ScalarOp::IntCmp(CmpKind::Eq),
                    Operand::Local(tag_value),
                    Operand::Const(Constant::Int(i64::from(tag))),
                    payloads,
                    failed,
                );
                self.switch_to(payloads);
                let extracted: Vec<Operand> = (0..fields.len())
                    .map(|index| {
                        let dest = self.fresh_local();
                        self.push(Inst::GetPayload {
                            dest,
                            src: scrutinee,
                            index: u16::try_from(index).unwrap_or_default(),
                        });
                        Operand::Local(dest)
                    })
                    .collect();
                self.test_all(fields, &extracted, &payload_tys, matched, failed)
            }
            PatternKind::Or(alternatives) => {
                // Every alternative binds the same names (the checker
                // agreed them); alternatives share one local per name.
                for alternative in alternatives {
                    for symbol in pattern_bind_symbols(alternative) {
                        if !self.locals.contains_key(&symbol) {
                            let local = self.fresh_local();
                            self.locals.insert(symbol, local);
                        }
                    }
                }
                for (ix, alternative) in alternatives.iter().enumerate() {
                    let last = ix + 1 == alternatives.len();
                    let next = if last { failed } else { self.new_block() };
                    self.compile_pattern_test(alternative, scrutinee, scrutinee_ty, matched, next)?;
                    if !last {
                        self.switch_to(next);
                    }
                }
                Ok(())
            }
            PatternKind::LiteralCharacter(text) => {
                // A Character shares the string views' {storage, start,
                // byte_count} shape, so the byte-comparison test serves
                // grapheme patterns too.
                let bytes = crate::parsing::lexing::unescape(text)
                    .map_err(|_| {
                        BackendError::new("invalid character escape".into(), pattern.span)
                    })?
                    .into_bytes();
                self.compile_string_pattern_test(
                    scrutinee,
                    scrutinee_ty,
                    bytes,
                    matched,
                    failed,
                    pattern.span,
                )
            }
            PatternKind::LiteralString(text) => {
                let bytes = crate::parsing::lexing::unescape(text)
                    .map_err(|_| BackendError::new("invalid string escape".into(), pattern.span))?
                    .into_bytes();
                self.compile_string_pattern_test(
                    scrutinee,
                    scrutinee_ty,
                    bytes,
                    matched,
                    failed,
                    pattern.span,
                )
            }
            PatternKind::Record { fields } => {
                let cells = self.record_cells(pattern, fields, scrutinee_ty)?;
                let extracted = self.extract_tuple(scrutinee, cells.len());
                // `label: pattern` also binds the label to the slot;
                // register those binders exactly like Bind cells.
                for (cell, slot) in cells.iter().zip(&extracted) {
                    let Some(symbol) = cell.bind.as_ref().and_then(|name| name.symbol().ok())
                    else {
                        continue;
                    };
                    let local = match self.locals.get(&symbol) {
                        Some(local) => *local,
                        None => {
                            let local = self.fresh_local();
                            self.locals.insert(symbol, local);
                            local
                        }
                    };
                    self.push(Inst::Copy {
                        dest: local,
                        src: *slot,
                    });
                }
                let patterns: Vec<Pattern> =
                    cells.iter().map(|cell| cell.pattern.clone()).collect();
                let tys: Vec<Ty> = cells.iter().map(|cell| cell.field_ty.clone()).collect();
                self.test_all(&patterns, &extracted, &tys, matched, failed)
            }
            PatternKind::Struct {
                fields,
                field_names,
                ..
            } => {
                let (heap, cells) =
                    self.struct_cells(pattern, fields, field_names, scrutinee_ty)?;
                let extracted = self.extract_struct_fields(scrutinee, heap, cells.len());
                let patterns: Vec<Pattern> =
                    cells.iter().map(|cell| cell.pattern.clone()).collect();
                let tys: Vec<Ty> = cells.iter().map(|cell| cell.field_ty.clone()).collect();
                self.test_all(&patterns, &extracted, &tys, matched, failed)
            }
            _ => Err(BackendError::unsupported(
                "this pattern is not supported yet".into(),
                pattern.span,
            )),
        }
    }

    /// A string-literal pattern is an equality chain over the scrutinee's
    /// bytes against the literal's immortal static bytes: length first,
    /// then one byte-compare loop.
    fn compile_string_pattern_test(
        &mut self,
        scrutinee: Operand,
        scrutinee_ty: &Ty,
        bytes: Vec<u8>,
        matched: BlockId,
        failed: BlockId,
        span: Span,
    ) -> Result<(), BackendError> {
        let mut head_ty = scrutinee_ty.clone();
        while let Ty::Borrow(_, inner) = head_ty {
            head_ty = *inner;
        }
        let Ty::Nominal(head, _) = &head_ty else {
            return Err(BackendError::unsupported(
                "string patterns on this scrutinee are not supported yet".into(),
                span,
            ));
        };
        let head = canonical(*head, self.program_builder.programs[self.program].module);
        let count_index = self
            .program_builder
            .field_index_by_name(head, "byte_count")
            .ok_or_else(|| {
                BackendError::unsupported(
                    "string patterns on this scrutinee are not supported yet".into(),
                    span,
                )
            })?;
        let storage_index = self
            .program_builder
            .field_index_by_name(head, "storage")
            .ok_or_else(|| {
                BackendError::unsupported(
                    "string patterns on this scrutinee are not supported yet".into(),
                    span,
                )
            })?;
        let start_index = self.program_builder.field_index_by_name(head, "start");

        let len = i64::try_from(bytes.len()).unwrap_or_default();
        let count = self.fresh_local();
        self.push(Inst::GetField {
            dest: count,
            src: scrutinee,
            index: count_index,
        });
        let count_ok = self.new_block();
        self.branch_if_equal(
            ScalarOp::IntCmp(CmpKind::Eq),
            Operand::Local(count),
            Operand::Const(Constant::Int(len)),
            count_ok,
            failed,
        );
        self.switch_to(count_ok);
        if bytes.is_empty() {
            self.terminate(Term::Goto(matched, Vec::new()));
            return Ok(());
        }

        let storage = self.fresh_local();
        self.push(Inst::GetField {
            dest: storage,
            src: scrutinee,
            index: storage_index,
        });
        let base = self.fresh_local();
        self.push(Inst::GetField {
            dest: base,
            src: Operand::Local(storage),
            index: 0,
        });
        let base = if let Some(start_index) = start_index {
            // A view (Substring) offsets into its shared storage.
            let start = self.fresh_local();
            self.push(Inst::GetField {
                dest: start,
                src: scrutinee,
                index: start_index,
            });
            let offset = self.fresh_local();
            self.push(Inst::PtrAdd {
                dest: offset,
                ptr: Operand::Local(base),
                offset: Operand::Local(start),
                size: 1,
            });
            offset
        } else {
            base
        };
        let literal = self.fresh_local();
        self.push(Inst::BytesLit {
            dest: literal,
            bytes,
        });

        let index = self.fresh_local();
        self.push(Inst::Copy {
            dest: index,
            src: Operand::Const(Constant::Int(0)),
        });
        let header = self.new_block();
        let body = self.new_block();
        self.terminate(Term::Goto(header, Vec::new()));

        self.switch_to(header);
        let in_range = self.fresh_local();
        self.push(Inst::Scalar {
            dest: in_range,
            op: ScalarOp::IntCmp(CmpKind::Lt),
            a: Operand::Local(index),
            b: Some(Operand::Const(Constant::Int(len))),
        });
        self.terminate(Term::Branch {
            cond: Operand::Local(in_range),
            then_block: body,
            else_block: matched,
        });

        self.switch_to(body);
        let lhs_ptr = self.fresh_local();
        self.push(Inst::PtrAdd {
            dest: lhs_ptr,
            ptr: Operand::Local(base),
            offset: Operand::Local(index),
            size: 1,
        });
        let rhs_ptr = self.fresh_local();
        self.push(Inst::PtrAdd {
            dest: rhs_ptr,
            ptr: Operand::Local(literal),
            offset: Operand::Local(index),
            size: 1,
        });
        let lhs = self.fresh_local();
        self.push(Inst::Load {
            dest: lhs,
            ptr: Operand::Local(lhs_ptr),
            kind: MemTy::Byte,
        });
        let rhs = self.fresh_local();
        self.push(Inst::Load {
            dest: rhs,
            ptr: Operand::Local(rhs_ptr),
            kind: MemTy::Byte,
        });
        let advance = self.new_block();
        self.branch_if_equal(
            ScalarOp::ByteCmp(CmpKind::Eq),
            Operand::Local(lhs),
            Operand::Local(rhs),
            advance,
            failed,
        );
        self.switch_to(advance);
        let bumped = self.fresh_local();
        self.push(Inst::Scalar {
            dest: bumped,
            op: ScalarOp::IntAdd,
            a: Operand::Local(index),
            b: Some(Operand::Const(Constant::Int(1))),
        });
        self.push(Inst::Copy {
            dest: index,
            src: Operand::Local(bumped),
        });
        self.terminate(Term::Goto(header, Vec::new()));
        Ok(())
    }

    /// Extract every element of a tuple scrutinee into fresh locals.
    fn extract_tuple(&mut self, scrutinee: Operand, len: usize) -> Vec<Operand> {
        (0..len)
            .map(|index| {
                let dest = self.fresh_local();
                self.push(Inst::TupleGet {
                    dest,
                    src: scrutinee,
                    index: u16::try_from(index).unwrap_or_default(),
                });
                Operand::Local(dest)
            })
            .collect()
    }

    /// Test sub-patterns in sequence; all must match.
    fn test_all(
        &mut self,
        patterns: &[Pattern],
        scrutinees: &[Operand],
        scrutinee_tys: &[Ty],
        matched: BlockId,
        failed: BlockId,
    ) -> Result<(), BackendError> {
        let mut next = matched;
        // Compile in reverse so each test falls through to the next one.
        let mut tests: Vec<BlockId> = Vec::new();
        for _ in 1..patterns.len() {
            tests.push(self.new_block());
        }
        if patterns.is_empty() {
            self.terminate(Term::Goto(matched, Vec::new()));
            return Ok(());
        }
        for (ix, ((pattern, scrutinee), scrutinee_ty)) in patterns
            .iter()
            .zip(scrutinees)
            .zip(scrutinee_tys)
            .enumerate()
        {
            next = *tests.get(ix).unwrap_or(&matched);
            self.compile_pattern_test(pattern, *scrutinee, scrutinee_ty, next, failed)?;
            if next != matched {
                self.switch_to(next);
            }
        }
        let _ = next;
        Ok(())
    }

    /// Emit a comparison and branch to `matched` on equality.
    fn branch_if_equal(
        &mut self,
        op: ScalarOp,
        a: Operand,
        b: Operand,
        matched: BlockId,
        failed: BlockId,
    ) {
        let cond = self.fresh_local();
        self.push(Inst::Scalar {
            dest: cond,
            op,
            a,
            b: Some(b),
        });
        self.terminate(Term::Branch {
            cond: Operand::Local(cond),
            then_block: matched,
            else_block: failed,
        });
    }

    /// Call through a function value. `mut` (exclusive-borrow) parameters
    /// follow the same writeback convention as direct calls, derived from
    /// the function type alone (function values have no receiver).
    fn compile_indirect_call(
        &mut self,
        callee_value: Operand,
        expr: &Expr,
        callee: &Expr,
        args: &[crate::typed_ast::CallArg],
    ) -> Result<Operand, BackendError> {
        let mut operands = Vec::new();
        let mut mut_arg_places: Vec<(usize, PlaceChain)> = Vec::new();
        self.compile_call_args(args, &mut operands, &mut mut_arg_places)?;
        let callee_ty = self.resolved(&callee.ty);
        if let Ty::Func(params, _, _) = &callee_ty {
            for (operand, param) in operands.iter().zip(params) {
                if !matches!(param, Ty::Borrow(_, _)) {
                    self.consume_operand(*operand);
                }
            }
        }
        let targets =
            self.writeback_targets(&callee_ty, operands.len(), None, &mut_arg_places, args, 0)?;
        let dest = self.fresh_local();
        let unwind = None;
        self.push(Inst::CallIndirect {
            dest,
            callee: callee_value,
            args: operands,
            unwind,
        });
        self.apply_writebacks(dest, targets, &self.resolved(&expr.ty), expr.span)
    }

    fn compile_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        args: &[crate::typed_ast::CallArg],
    ) -> Result<Operand, BackendError> {
        // A generic callee monomorphizes against the frontend's recorded
        // instantiation, resolved through this instance's own substitution.
        // Any residual type parameter means the call cannot specialize yet.
        let mut subst: Vec<(Symbol, Ty)> = Vec::new();
        for instantiation in [&callee.instantiation, &expr.instantiation] {
            let Some(instantiation) = instantiation else {
                continue;
            };
            for (param, ty) in instantiation {
                subst.push((*param, self.resolved(ty)));
            }
        }

        let mut operands = Vec::new();
        let mut receiver_place: Option<PlaceChain> = None;
        let mut value_receiver_ty: Option<Ty> = None;
        let target = match &callee.kind {
            ExprKind::Constructor(_) => {
                return self.compile_construction(expr, callee, args, subst);
            }
            ExprKind::Variable(Name::Resolved(symbol, _)) if self.locals.contains_key(symbol) => {
                // A function value in a local: indirect call. A celled
                // binder (letrec) reads the current closure first.
                let local = self.locals[symbol];
                let callee_value = if self.cell_handles.contains(&local) {
                    let dest = self.fresh_local();
                    self.push(Inst::CellGet {
                        dest,
                        cell: Operand::Local(local),
                    });
                    Operand::Local(dest)
                } else {
                    Operand::Local(local)
                };
                return self.compile_indirect_call(callee_value, expr, callee, args);
            }
            ExprKind::Variable(Name::Resolved(symbol, _))
                if !self.program_builder.callables.contains_key(&canonical(
                    *symbol,
                    self.program_builder.programs[self.program].module,
                )) && self.program_builder.global_slots.contains_key(symbol) =>
            {
                // A function value in a global slot: load and call
                // indirectly.
                let loaded = self.fresh_local();
                let slot = self.program_builder.global_slots[symbol];
                self.push(Inst::GlobalLoad {
                    dest: loaded,
                    global: slot,
                });
                return self.compile_indirect_call(Operand::Local(loaded), expr, callee, args);
            }
            ExprKind::Variable(Name::Resolved(symbol, _)) => *symbol,
            ExprKind::Member(receiver, label) => {
                let Some(resolution) = &callee.member_resolution else {
                    return Err(BackendError::new(
                        "member call without a frontend resolution".into(),
                        callee.span,
                    ));
                };
                // A `Constructor` receiver is a type-level reference
                // (operator desugaring dispatches `Add.add(a, b)` through
                // the protocol); it contributes no runtime operand.
                let value_receiver = receiver
                    .as_deref()
                    .filter(|receiver| !matches!(receiver.kind, ExprKind::Constructor(_)));
                // A call on `any P` dispatches through the value's witness
                // table: fixed slots 0/1, requirements from 2.
                if let Some(receiver) = value_receiver {
                    let mut receiver_ty = self.resolved(&receiver.ty);
                    while let Ty::Borrow(_, inner) = receiver_ty {
                        receiver_ty = *inner;
                    }
                    if let Ty::Any {
                        protocol: any_protocol,
                        ..
                    } = &receiver_ty
                    {
                        let module = self.program_builder.programs[self.program].module;
                        let protocol = canonical(any_protocol.protocol, module);
                        let crate::label::Label::Named(name) = label else {
                            return Err(BackendError::unsupported(
                                "positional members on existentials are not supported yet".into(),
                                callee.span,
                            ));
                        };
                        let index = self
                            .program_builder
                            .protocol_requirements(protocol)
                            .and_then(|requirements| {
                                requirements.iter().position(|slot| slot == name)
                            })
                            .ok_or_else(|| {
                                BackendError::new(
                                    "existential member without a requirement slot".into(),
                                    callee.span,
                                )
                            })?;
                        // A `mut func` requirement evolves the payload; the
                        // call returns `(result, final payload)` and the
                        // existential rebuilds around the evolved payload
                        // with its own witness table, then writes back.
                        let mut_requirement = self.requirement_is_mut(protocol, name);
                        let receiver_chain = if mut_requirement {
                            let Some(chain) = self.resolve_place(receiver)? else {
                                return Err(BackendError::unsupported(
                                    "a `mut` requirement on an existential that is not a named place is not supported yet"
                                        .into(),
                                    callee.span,
                                ));
                            };
                            Some(chain)
                        } else {
                            None
                        };
                        let value = self.compile_expr(receiver)?;
                        let witness = self.fresh_local();
                        self.push(Inst::ExistentialWitness {
                            dest: witness,
                            src: value,
                            index: u16::try_from(index + 2).unwrap_or_default(),
                        });
                        let payload = self.fresh_local();
                        self.push(Inst::ExistentialPayload {
                            dest: payload,
                            src: value,
                        });
                        let receiver_target = match receiver_chain {
                            Some(chain) => {
                                let count = self
                                    .program_builder
                                    .protocol_requirements(protocol)
                                    .map(|requirements| requirements.len())
                                    .unwrap_or(0);
                                let mut witnesses = Vec::new();
                                for slot in 0..(2 + count) {
                                    let entry = self.fresh_local();
                                    self.push(Inst::ExistentialWitness {
                                        dest: entry,
                                        src: value,
                                        index: u16::try_from(slot).unwrap_or_default(),
                                    });
                                    witnesses.push(Operand::Local(entry));
                                }
                                Some(Some(WritebackTarget::Repack {
                                    chain,
                                    protocol,
                                    witnesses,
                                }))
                            }
                            None => None,
                        };
                        let mut operands = vec![Operand::Local(payload)];
                        let mut mut_arg_places: Vec<(usize, PlaceChain)> = Vec::new();
                        self.compile_call_args(args, &mut operands, &mut mut_arg_places)?;
                        let callee_ty = self.resolved(&callee.ty);
                        // Owned arguments transfer to the callee, the same
                        // as direct calls (offset-aligned: member callee
                        // types exclude the receiver).
                        if let Ty::Func(params, _, _) = &callee_ty {
                            let offset = operands.len().saturating_sub(params.len());
                            for (ix, param) in params.iter().enumerate() {
                                if !matches!(param, Ty::Borrow(_, _)) {
                                    self.consume_into(operands[offset + ix], param, expr.span)?;
                                }
                            }
                        }
                        let targets = self.writeback_targets(
                            &callee_ty,
                            operands.len(),
                            receiver_target,
                            &mut_arg_places,
                            args,
                            1,
                        )?;
                        let dest = self.fresh_local();
                        let unwind = None;
                        self.push(Inst::CallIndirect {
                            dest,
                            callee: Operand::Local(witness),
                            args: operands,
                            unwind,
                        });
                        return self.apply_writebacks(
                            dest,
                            targets,
                            &self.resolved(&expr.ty),
                            expr.span,
                        );
                    }
                }
                let symbol = match resolution {
                    crate::types::output::MemberResolution::Direct(symbol) => *symbol,
                    resolution @ (crate::types::output::MemberResolution::ViaConformance {
                        ..
                    }
                    | crate::types::output::MemberResolution::ViaRequirement {
                        ..
                    }) => {
                        let (protocol, witness, evidence_substitution) = match resolution {
                            crate::types::output::MemberResolution::ViaConformance {
                                protocol,
                                witness,
                                substitution,
                                ..
                            } => (protocol, witness, Some(substitution)),
                            crate::types::output::MemberResolution::ViaRequirement {
                                protocol,
                                requirement,
                                ..
                            } => (protocol, requirement, None),
                            crate::types::output::MemberResolution::Direct(_) => unreachable!(),
                        };
                        let self_ty = match (value_receiver, args.first()) {
                            (Some(receiver), _) => self.resolved(&receiver.ty),
                            (None, Some(arg)) => self.resolved(&arg.value.ty),
                            (None, None) => self.resolved(&callee.ty),
                        };
                        let mut self_ty = self_ty;
                        while let Ty::Borrow(_, inner) = self_ty {
                            self_ty = *inner;
                        }
                        // The resolution is written in this program's
                        // view; canonicalize before matching rows.
                        let module = self.program_builder.programs[self.program].module;
                        let protocol = crate::types::ty::ProtocolRef {
                            protocol: canonical(protocol.protocol, module),
                            args: protocol
                                .args
                                .iter()
                                .map(|arg| canonical_ty(arg, module))
                                .collect(),
                        };
                        let protocol = &protocol;
                        // A rigid receiver dispatches through the frame's
                        // conformance dictionary, like `any P` dispatches
                        // through its witness table.
                        if let Ty::Param(rigid) = &self_ty {
                            let rigid = &self.canon_rigid(*rigid);
                            let crate::label::Label::Named(name) = label else {
                                return Err(BackendError::unsupported(
                                    "positional members on generic values are not supported yet"
                                        .into(),
                                    callee.span,
                                ));
                            };
                            let index = self
                                .program_builder
                                .protocol_requirements(protocol.protocol)
                                .and_then(|requirements| {
                                    requirements.iter().position(|slot| slot == name)
                                })
                                .ok_or_else(|| {
                                    BackendError::new(
                                        "generic member without a requirement slot".into(),
                                        callee.span,
                                    )
                                })?;
                            let Some(dictionary) = self
                                .param_requirements
                                .get(&(*rigid, protocol.protocol))
                                .cloned()
                            else {
                                return Err(BackendError::unsupported(
                                    "a generic value cannot cross this boundary without its conformance dictionaries (not supported yet)"
                                        .into(),
                                    callee.span,
                                ));
                            };
                            // A `mut func` requirement (declared mode, so
                            // every implementation follows the writeback
                            // convention) returns `(result, final self,
                            // final mut values…)`; the shared machinery
                            // lands each into its place.
                            let mut_requirement = self.requirement_is_mut(protocol.protocol, name);
                            let receiver_target = if mut_requirement {
                                let Some(receiver) = value_receiver else {
                                    return Err(BackendError::new(
                                        "`mut` requirement without a receiver".into(),
                                        callee.span,
                                    ));
                                };
                                let Some(chain) = self.resolve_place(receiver)? else {
                                    return Err(BackendError::unsupported(
                                        "a `mut` requirement on a generic value that is not a named place is not supported yet"
                                            .into(),
                                        callee.span,
                                    ));
                                };
                                Some(Some(WritebackTarget::Place(chain)))
                            } else {
                                None
                            };
                            let implementation = dictionary[index];
                            let mut operands = Vec::new();
                            if let Some(receiver) = value_receiver {
                                operands.push(self.compile_expr(receiver)?);
                            }
                            let mut mut_arg_places: Vec<(usize, PlaceChain)> = Vec::new();
                            self.compile_call_args(args, &mut operands, &mut mut_arg_places)?;
                            let callee_ty = self.resolved(&callee.ty);
                            // Owned arguments transfer to the callee, the
                            // same as direct calls (offset-aligned: member
                            // callee types exclude the receiver).
                            if let Ty::Func(params, _, _) = &callee_ty {
                                let offset = operands.len().saturating_sub(params.len());
                                for (ix, param) in params.iter().enumerate() {
                                    if !matches!(param, Ty::Borrow(_, _)) {
                                        self.consume_into(operands[offset + ix], param, expr.span)?;
                                    }
                                }
                            }
                            let args_operand_offset = usize::from(value_receiver.is_some());
                            let targets = self.writeback_targets(
                                &callee_ty,
                                operands.len(),
                                receiver_target,
                                &mut_arg_places,
                                args,
                                args_operand_offset,
                            )?;
                            let dest = self.fresh_local();
                            let unwind = None;
                            self.push(Inst::CallIndirect {
                                dest,
                                callee: Operand::Local(implementation),
                                args: operands,
                                unwind,
                            });
                            return self.apply_writebacks(
                                dest,
                                targets,
                                &self.resolved(&expr.ty),
                                expr.span,
                            );
                        }
                        if let Some(evidence_substitution) = evidence_substitution {
                            // Typing published this substitution in the
                            // generic body's own terms; the instance
                            // substitution makes it concrete here.
                            subst.extend(evidence_substitution.iter().map(|(symbol, ty)| {
                                (
                                    canonical(*symbol, module),
                                    self.resolved(&canonical_ty(ty, module)),
                                )
                            }));
                            canonical(*witness, module)
                        } else if let Some((implementation, row_subst)) = self
                            .program_builder
                            .conformance_witness(&self_ty, protocol, label)
                        {
                            // Deferred selection (ADR 0036): the receiver
                            // was rigid at typing, so no per-node commitment
                            // could name the witness. The instance
                            // substitution has made it concrete here, and
                            // coherence makes the shared selector's answer
                            // forced — this dereferences typing's decision,
                            // it does not make a new one.
                            subst.extend(row_subst);
                            implementation
                        } else if !self
                            .program_builder
                            .callables
                            .contains_key(&canonical(*witness, module))
                            && matches!(label, crate::label::Label::Named(name) if name == "equals" || name == "show")
                        {
                            // Typing published structural derivation rather
                            // than a conformance row; synthesize that chosen
                            // implementation without searching the catalog.
                            let derived_show =
                                matches!(label, crate::label::Label::Named(name) if name == "show");
                            let glue = if derived_show {
                                self.program_builder
                                    .derived_show(&self_ty, protocol, expr.span)?
                            } else {
                                self.program_builder
                                    .derived_equality(&self_ty, protocol, expr.span)?
                            };
                            let mut operands = Vec::new();
                            if let Some(receiver) = value_receiver {
                                operands.push(self.compile_expr(receiver)?);
                            }
                            for arg in args {
                                operands.push(self.compile_expr(&arg.value)?);
                            }
                            let dest = self.fresh_local();
                            self.push_call(dest, glue, operands);
                            self.produce_temp(dest, &self.resolved(&expr.ty));
                            return Ok(Operand::Local(dest));
                        } else {
                            // The requirement's default body executes with
                            // `Self`, the protocol's input parameters, and
                            // the conformance's associated types
                            // substituted.
                            subst.push((protocol.protocol, self_ty.clone()));
                            if let Some(params) =
                                self.program_builder.protocol_params(protocol.protocol)
                            {
                                for (param, arg) in params.iter().zip(&protocol.args) {
                                    subst.push((*param, self.resolved(arg)));
                                }
                            }
                            subst.extend(self.program_builder.conformance_assoc(&self_ty, protocol));
                            canonical(*witness, module)
                        }
                    }
                };
                if let Some(receiver) = value_receiver {
                    value_receiver_ty = Some(self.resolved(&receiver.ty));
                    // A `mut func` callee writes its evolved receiver back
                    // into this place — a binding, a global, or a
                    // projection spine (`self.comments.push(…)`).
                    receiver_place = self.resolve_place(receiver)?;
                    let compiled = self.compile_expr(receiver)?;
                    operands.push(compiled);
                }
                symbol
            }
            _ => {
                // Any other callee is a function VALUE (a field read, a
                // block value): compile it and call indirectly.
                let callee_value = self.compile_expr(callee)?;
                return self.compile_indirect_call(callee_value, expr, callee, args);
            }
        };

        let mut mut_arg_places: Vec<(usize, PlaceChain)> = Vec::new();
        self.compile_call_args(args, &mut operands, &mut mut_arg_places)?;

        let target = canonical(target, self.program_builder.programs[self.program].module);
        // Non-borrow parameters take ownership: the callee drops them.
        // Typing selected the modes; the callee's function type records
        // them (borrow-by-default, ADR 0018). A member callee's type may
        // exclude the receiver: align from the right, and consume the
        // receiver only for `consuming func` methods.
        if let Ty::Func(params, _, _) = &self.resolved(&callee.ty) {
            let params = params.clone();
            let offset = operands.len().saturating_sub(params.len());
            for (operand, param) in operands[offset..].to_vec().iter().zip(&params) {
                if !matches!(param, Ty::Borrow(_, _)) {
                    self.consume_into(*operand, param, expr.span)?;
                }
            }
            // Call-site markers must match the declared modes (ADR 0018).
            let marker_params = &params[params.len().saturating_sub(args.len())..];
            for (arg, param) in args.iter().zip(marker_params) {
                match arg.mode {
                    Some(ArgMode::Mut) if !matches!(param, Ty::Borrow(Perm::Exclusive, _)) => {
                        return Err(BackendError::new(
                            "the `mut` marker requires a `mut` parameter".into(),
                            arg.value.span,
                        ));
                    }
                    Some(ArgMode::Borrow) if !matches!(param, Ty::Borrow(_, _)) => {
                        return Err(BackendError::new(
                            "the `borrow` marker requires a borrowing parameter".into(),
                            arg.value.span,
                        ));
                    }
                    _ => {}
                }
            }
            if offset == 1
                && self
                    .program_builder
                    .callables
                    .get(&target)
                    .is_some_and(|callable| {
                        matches!(
                            callable.receiver,
                            crate::node_kinds::decl::ReceiverMode::Consuming
                        )
                    })
            {
                let receiver = operands[0];
                let receiver_ty = value_receiver_ty.clone().unwrap_or(Ty::Error);
                self.consume_into(receiver, &receiver_ty, expr.span)?;
            }
        }
        let mut_receiver = self
            .program_builder
            .callables
            .get(&target)
            .is_some_and(|callable| {
                matches!(
                    callable.receiver,
                    crate::node_kinds::decl::ReceiverMode::Ref
                )
            });
        // Mirror the callee's writeback order: `mut` receiver first, then
        // `mut` (exclusive-borrow) parameters in declaration order.
        if mut_receiver
            && let Some(chain) = &receiver_place
            && self
                .local_tys
                .get(&chain.base)
                .is_some_and(|base_ty| matches!(base_ty, Ty::Borrow(Perm::Shared, _)))
        {
            return Err(BackendError::new(
                "cannot call a `mut func` through a shared borrow".into(),
                callee.span,
            ));
        }
        // Protocol-static calls spell the receiver as their first argument,
        // so its exclusive-borrow parameter must drive writeback below. Only
        // reserve the separate receiver slot for an actual value-member call.
        let receiver = (mut_receiver && value_receiver_ty.is_some())
            .then(|| receiver_place.clone().map(WritebackTarget::Place));
        let callee_ty = self.resolved(&callee.ty);
        let args_operand_offset = usize::from(value_receiver_ty.is_some());
        let targets = self.writeback_targets(
            &callee_ty,
            operands.len(),
            receiver,
            &mut_arg_places,
            args,
            args_operand_offset,
        )?;
        // A `mut` argument (marked or not) or receiver mutates its
        // place: live views of that place die here, and later reads of
        // them reject.
        let mutated_bases: Vec<LocalId> = targets
            .iter()
            .flatten()
            .map(|target| match target {
                WritebackTarget::Place(chain) => chain.base,
                WritebackTarget::Repack { chain, .. } => chain.base,
            })
            .collect();
        for base in mutated_bases {
            // A live shared view keeps a snapshot across the mutation:
            // retain the pre-call value into an anonymous scope-owned
            // binding (the callee round-trips its own reference; the
            // displaced one dies at scope exit). Without a live view
            // the old invalidation is simply unnecessary bookkeeping —
            // there is nobody left to invalidate.
            if let Some(ty) = self.owned_tys.get(&base).cloned()
                && self.has_live_view(base)
            {
                if let Err(error) = self.retain_value(Operand::Local(base), &ty, expr.span) {
                    self.deferred_errors.push(error);
                }
                let displaced = self.fresh_local();
                self.push(Inst::Copy {
                    dest: displaced,
                    src: Operand::Local(base),
                });
                self.own_local(displaced, &ty);
                let views: Vec<LocalId> = self
                    .borrow_roots
                    .iter()
                    .filter(|(_, root)| **root == base)
                    .map(|(view, _)| *view)
                    .collect();
                for view in views {
                    self.borrow_roots.insert(view, displaced);
                }
            }
            self.loans.retain(|loan| loan.root != base);
        }
        let func = self.demand_specialized(target, subst, expr.span)?;
        self.program_builder
            .writeback_expectations
            .push((func, targets.len(), expr.span));
        self.append_witness_args(func, &mut operands, expr.span)?;
        let dest = self.fresh_local();
        let first_operand = operands.first().copied();
        self.push_call(dest, func, operands);
        let result = self.apply_writebacks(dest, targets, &self.resolved(&expr.ty), expr.span)?;
        // A call returning a borrowed view derives from its receiver or
        // first argument: the view's owner for invalidation and escape
        // checks (per-argument provenance, RFC 2094's model).
        let result_ty = self.resolved(&expr.ty);
        if (matches!(result_ty, Ty::Borrow(_, _))
            || borrow_classified(self.program_builder, &result_ty))
            && let Some(first) = first_operand
        {
            self.record_view(result, first);
            if let Operand::Local(view) = result {
                self.view_locals.insert(view);
            }
        }
        Ok(result)
    }

    /// Pack a value into `any P`: the payload plus `[drop, retain,
    /// requirement…]` witness closures, each selected from the payload's
    /// conformance the way a static call would be.
    fn compile_existential_pack(
        &mut self,
        expr: &Expr,
        pack: &crate::types::output::ExistentialPack,
        payload: Operand,
    ) -> Result<Operand, BackendError> {
        let payload_ty = self.resolved(&pack.payload);
        let existential_ty = self.resolved(&pack.existential);
        let Ty::Any { protocol, .. } = &existential_ty else {
            return Err(BackendError::new(
                "existential coercion without an existential type".into(),
                expr.span,
            ));
        };
        let module = self.program_builder.programs[self.program].module;
        let protocol = crate::types::ty::ProtocolRef {
            protocol: canonical(protocol.protocol, module),
            args: protocol
                .args
                .iter()
                .map(|arg| canonical_ty(arg, module))
                .collect(),
        };

        // A `'heap` payload's region cannot escape into an existential:
        // the witness table has no region claim to carry.
        if contains_object(self.program_builder, &payload_ty) {
            return Err(BackendError::new(
                "a `'heap` value cannot be stored in an existential".into(),
                expr.span,
            ));
        }
        // A rigid payload's witness table IS the frame's dictionary: the
        // `[drop, retain]` pair plus the constraint protocol's requirement
        // closures, already selected at the perform site.
        if let Ty::Param(rigid) = &payload_ty {
            let rigid = self.canon_rigid(*rigid);
            let Some((drop_witness, retain_witness)) = self.param_witnesses.get(&rigid).copied()
            else {
                return Err(BackendError::unsupported(
                    "a generic value cannot cross this boundary without its ownership witnesses (not supported yet)"
                        .into(),
                    expr.span,
                ));
            };
            let Some(requirements) = self
                .param_requirements
                .get(&(rigid, protocol.protocol))
                .cloned()
            else {
                return Err(BackendError::unsupported(
                    "a generic value cannot cross this boundary without its conformance dictionaries (not supported yet)"
                        .into(),
                    expr.span,
                ));
            };
            let mut witnesses = vec![Operand::Local(drop_witness), Operand::Local(retain_witness)];
            witnesses.extend(requirements.into_iter().map(Operand::Local));
            self.consume_operand(payload);
            let dest = self.fresh_local();
            self.push(Inst::ExistentialPack {
                dest,
                protocol: protocol.protocol,
                payload,
                witnesses,
            });
            self.produce_temp(dest, &existential_ty);
            return Ok(Operand::Local(dest));
        }

        let mut witnesses = Vec::new();
        let drop_glue = self.program_builder.value_glue(&payload_ty, Glue::Drop)?;
        let drop_closure = self.fresh_local();
        self.push(Inst::MakeClosure {
            dest: drop_closure,
            func: drop_glue,
            env: Vec::new(),
        });
        witnesses.push(Operand::Local(drop_closure));
        let retain_glue = self.program_builder.value_glue(&payload_ty, Glue::Retain)?;
        let retain_closure = self.fresh_local();
        self.push(Inst::MakeClosure {
            dest: retain_closure,
            func: retain_glue,
            env: Vec::new(),
        });
        witnesses.push(Operand::Local(retain_closure));

        let requirements = self
            .program_builder
            .protocol_requirements(protocol.protocol)
            .ok_or_else(|| {
                BackendError::new(
                    "existential protocol without a catalog entry".into(),
                    expr.span,
                )
            })?;
        for name in requirements {
            let closure = self.requirement_closure(&payload_ty, &protocol, &name, expr.span)?;
            witnesses.push(closure);
        }

        self.consume_operand(payload);
        let dest = self.fresh_local();
        self.push(Inst::ExistentialPack {
            dest,
            protocol: protocol.protocol,
            payload,
            witnesses,
        });
        self.produce_temp(dest, &existential_ty);
        Ok(Operand::Local(dest))
    }

    /// Lower `'io(request)` to a tag dispatch over the request enum: one
    /// host operation per variant, in declaration order (which matches the
    /// runtime's operation table one-to-one). Unused operand slots pass
    /// zero; the host never reads them.
    fn compile_io_perform(
        &mut self,
        expr: &Expr,
        args: &[crate::typed_ast::CallArg],
    ) -> Result<Operand, BackendError> {
        let [request] = args else {
            return Err(BackendError::new(
                "'io takes exactly one request".into(),
                expr.span,
            ));
        };
        let request_ty = self.resolved(&request.value.ty);
        let Ty::Nominal(request_enum, type_args) = &request_ty else {
            return Err(BackendError::new(
                "'io request must be the core request enum".into(),
                expr.span,
            ));
        };
        let Some(payloads) = self
            .program_builder
            .variant_payloads(*request_enum, type_args)
        else {
            return Err(BackendError::new(
                "'io request must be the core request enum".into(),
                expr.span,
            ));
        };
        let value = self.compile_expr(&request.value)?;
        let tag = self.fresh_local();
        self.push(Inst::GetTag {
            dest: tag,
            src: value,
        });
        let result = self.fresh_local();
        let join = self.new_block();
        let zero = Operand::Const(Constant::Int(0));
        for (variant, payload_tys) in payloads.iter().enumerate() {
            let arm = self.new_block();
            let next = self.new_block();
            self.branch_if_equal(
                ScalarOp::IntCmp(CmpKind::Eq),
                Operand::Local(tag),
                Operand::Const(Constant::Int(i64::try_from(variant).unwrap_or_default())),
                arm,
                next,
            );
            self.switch_to(arm);
            let mut operands = [zero, zero, zero];
            for (index, operand) in operands.iter_mut().take(payload_tys.len()).enumerate() {
                let payload = self.fresh_local();
                self.push(Inst::GetPayload {
                    dest: payload,
                    src: value,
                    index: u16::try_from(index).unwrap_or_default(),
                });
                *operand = Operand::Local(payload);
            }
            self.push(Inst::Io {
                dest: result,
                op: u8::try_from(variant).unwrap_or_default(),
                a: operands[0],
                b: operands[1],
                c: operands[2],
            });
            self.terminate(Term::Goto(join, Vec::new()));
            self.switch_to(next);
        }
        self.terminate(Term::Trap("unknown io request"));
        self.switch_to(join);
        Ok(Operand::Local(result))
    }

    /// Install a deep handler: reify the delimiter (this frame's return),
    /// compile the clause as a closure over `[delimiter, captures…]`, and
    /// push the handler entry. Entries pop with the frame.
    fn install_handler(&mut self, effect: Symbol, body: &Block) -> Result<(), BackendError> {
        // The runtime is the implicit handler for core's ambient effects
        // ('io, 'alloc, 'async): user handlers over them would be
        // silently bypassed, so they fail closed.
        if effect.module_id() == Some(crate::compiling::module::ModuleId::Core) {
            return Err(BackendError::unsupported(
                "user handlers over ambient core effects are not supported yet".into(),
                body.span,
            ));
        }
        let body_nodes: Vec<&Node> = body.body.iter().collect();
        let captured = free_locals(&body_nodes, &self.locals);
        let cont = self.fresh_local();
        self.push(Inst::MakeCont { dest: cont });

        let id = self.program_builder.reserve("handler_clause");
        // Clause binders are usually unannotated; their ownership comes
        // from the effect's declared parameter types (rigid generics stay
        // `Ty::Param` — released and retained through the witnesses the
        // perform site appends).
        let (declared_params, sig_generics) = match self.program_builder.effect_sig(effect) {
            Some((sig, sig_module)) => (
                sig.params
                    .iter()
                    .map(|param| canonical_ty(param, sig_module))
                    .collect::<Vec<_>>(),
                // Same TYPE-generic filter as the perform site: the
                // appended witness blocks and these bindings must agree.
                type_param_symbols(&sig.generics),
            ),
            None => (Vec::new(), Vec::new()),
        };
        // The clause inherits the enclosing frame's rigid witnesses and
        // dictionaries through its environment, exactly like an ordinary
        // closure (`capture_env`/`bind_env`): its body can drop, retain,
        // and dispatch on the enclosing function's generics. The effect's
        // own generics arrive as perform-site arguments instead.
        let inherited: Vec<(Symbol, (LocalId, LocalId))> = self
            .sorted_witnesses()
            .into_iter()
            .filter(|(symbol, _)| !sig_generics.contains(symbol))
            .collect();
        let mut inherited_env: Vec<Operand> = Vec::new();
        for (symbol, _) in &inherited {
            self.push_witness_block(*symbol, &mut inherited_env, body.span)?;
        }
        let mut fx = FunctionBuilder::new(self.program_builder, 0, self.program);
        fx.subst = self.subst.clone();
        // Clause bodies read last-use liveness like any frame: seed
        // their use counts (cell conversion stays the enclosing
        // frame's concern).
        let (_, _, clause_use_counts) = cell_scan(&body_nodes);
        fx.use_counts = clause_use_counts;
        let declared_arity = u16::try_from(body.args.len())
            .map_err(|_| BackendError::new("too many clause parameters".into(), body.span))?;
        // The perform site appends each generic's hidden block ([drop,
        // retain], then constraint dictionaries) after the declared
        // arguments.
        let arity = fx.bind_witness_params(&sig_generics, declared_arity);
        fx.next_local = arity;
        for (ix, param) in body.args.iter().enumerate() {
            let local = u16::try_from(ix).unwrap_or_default();
            let ty = match &param.ty {
                Some(ty) => Some(fx.resolved(ty)),
                None => declared_params.get(ix).cloned(),
            };
            if let Some(ty) = ty {
                // `mut` (exclusive-borrow) effect parameters resume with
                // their evolved values, the same writeback convention as
                // direct calls.
                if matches!(ty, Ty::Borrow(Perm::Exclusive, _)) {
                    fx.writeback_params.push(local);
                }
                fx.check_copy(&ty, body.span)?;
                fx.own_local(local, &ty);
            }
            if let Name::Resolved(symbol, _) = &param.name {
                fx.locals.insert(*symbol, local);
            }
        }
        let delimiter = fx.fresh_local();
        fx.push(Inst::EnvGet {
            dest: delimiter,
            index: 0,
        });
        fx.clause_delimiter = Some(delimiter);
        for (index, symbol) in captured.iter().enumerate() {
            let local = fx.fresh_local();
            fx.push(Inst::EnvGet {
                dest: local,
                index: u16::try_from(index + 1).unwrap_or_default(),
            });
            fx.locals.insert(*symbol, local);
        }
        // Rebind the inherited witness blocks in the same layout
        // `push_witness_block` appended them (the clause-frame mirror of
        // `bind_env`'s inherited section).
        let mut env_index = u16::try_from(1 + captured.len()).unwrap_or_default();
        for (param_symbol, _) in &inherited {
            let drop_local = fx.fresh_local();
            fx.push(Inst::EnvGet {
                dest: drop_local,
                index: env_index,
            });
            let retain_local = fx.fresh_local();
            fx.push(Inst::EnvGet {
                dest: retain_local,
                index: env_index + 1,
            });
            env_index += 2;
            fx.param_witnesses
                .insert(*param_symbol, (drop_local, retain_local));
            for protocol in fx.program_builder.rigid_constraints(*param_symbol) {
                let count = fx
                    .program_builder
                    .protocol_requirements(protocol.protocol)
                    .map(|requirements| requirements.len())
                    .unwrap_or(0);
                let mut locals = Vec::new();
                for _ in 0..count {
                    let local = fx.fresh_local();
                    fx.push(Inst::EnvGet {
                        dest: local,
                        index: env_index,
                    });
                    env_index += 1;
                    locals.push(local);
                }
                fx.param_requirements
                    .insert((*param_symbol, protocol.protocol), locals);
            }
        }
        let value = fx.compile_block(body)?;
        if !fx.terminated() {
            // A clause that finishes without `continue` discontinues: its
            // value becomes the delimiter frame's return (CHG-03), after
            // this clause's own cleanup.
            fx.emit_discontinue(Operand::Local(delimiter), value);
        }
        fx.elaborate_and_verify();
        fx.deferred_error()?;
        let (n_locals, blocks) = (fx.next_local, fx.blocks);
        self.program_builder.functions[id] = Function {
            name: "handler_clause".into(),
            arity,
            n_locals,
            blocks,
        };

        let mut env = vec![Operand::Local(cont)];
        env.extend(
            captured
                .iter()
                .filter_map(|symbol| self.locals.get(symbol).copied())
                .map(Operand::Local),
        );
        env.extend(inherited_env);
        let clause = self.fresh_local();
        self.push(Inst::MakeClosure {
            dest: clause,
            func: id,
            env,
        });
        self.push(Inst::PushHandler {
            effect,
            clause: Operand::Local(clause),
            cont: Operand::Local(cont),
        });
        Ok(())
    }

    /// A block used as a function value (a trailing block argument): its
    /// own chunk over `[captures…]`, parameters from the block's argument
    /// list.
    /// The capability for a user effect at this point: the captured
    /// creation-site handler when this frame is a closure carrying one
    /// (Effekt-style lexical capture — Brachthäuser, Schuster &
    /// Ostermann, OOPSLA 2020; ADR 0011 departure (d)), the dynamic
    /// nearest handler otherwise. Returns the handler's clause and its
    /// stack index (the search floor for the clause call's extent).
    fn capability(&mut self, effect: Symbol) -> (LocalId, LocalId) {
        if let Some(pair) = self.capabilities.get(&effect) {
            return *pair;
        }
        let clause = self.fresh_local();
        let cont = self.fresh_local();
        let index = self.fresh_local();
        self.push(Inst::FindHandler {
            clause,
            cont,
            index,
            effect,
        });
        (clause, index)
    }

    /// The user effects a function value may perform, from its resolved
    /// effect row — the effects whose capabilities the closure captures
    /// at creation. Ambient core effects dispatch to the host and carry
    /// no capability.
    fn closure_effects(&mut self, ty: &Ty) -> Vec<Symbol> {
        let module = self.program_builder.programs[self.program].module;
        let Ty::Func(_, _, row) = self.resolved(ty) else {
            return Vec::new();
        };
        row.effects
            .iter()
            .map(|entry| canonical(entry.effect, module))
            // The runtime implicitly handles ALL of core's ambient effects
            // ('io, 'alloc, 'async), and `install_handler` rejects user
            // handlers over them — so a closure never carries capabilities
            // for them (a FindHandler for one would trap). Only user
            // effects lexically capture their creation-site handler.
            .filter(|effect| effect.module_id() != Some(crate::compiling::module::ModuleId::Core))
            .collect()
    }

    /// The closure-environment contract, build side: captured frame
    /// values first (cell handles travel as handles), then this frame's
    /// rigid-generic witness pairs and conformance dictionaries in
    /// sorted order, then one `(clause, index)` capability per user
    /// effect the closure may perform. `bind_env` is the mirror; the
    /// two must agree on layout. New environment slot kinds are added
    /// here and there, nowhere else.
    fn capture_env(
        &mut self,
        captured: &[Symbol],
        effects: &[Symbol],
    ) -> Result<(Vec<Operand>, WitnessPairs), BackendError> {
        let mut env: Vec<Operand> = captured
            .iter()
            .filter_map(|symbol| self.locals.get(symbol).copied())
            .map(Operand::Local)
            .collect();
        let inherited = self.sorted_witnesses();
        for (param, (drop_witness, retain_witness)) in &inherited {
            env.push(Operand::Local(*drop_witness));
            env.push(Operand::Local(*retain_witness));
            for protocol in self.program_builder.rigid_constraints(*param) {
                let Some(locals) = self.param_requirements.get(&(*param, protocol.protocol)) else {
                    return Err(BackendError::unsupported(
                        "a generic value cannot cross this boundary without its conformance dictionaries (not supported yet)"
                            .into(),
                        Span::SYNTHESIZED,
                    ));
                };
                env.extend(locals.iter().map(|local| Operand::Local(*local)));
            }
        }
        for effect in effects {
            let (clause, index) = self.capability(*effect);
            env.push(Operand::Local(clause));
            env.push(Operand::Local(index));
        }
        Ok((env, inherited))
    }

    /// An anonymous or local function value: its body compiles as its own
    /// chunk; free locals capture by value into the environment
    /// (handler-extent shared borrows in v1). The chunk's prologue reads
    /// each capture back out of the environment.
    fn compile_closure(&mut self, func: &Func, ty: &Ty) -> Result<Operand, BackendError> {
        let body_nodes: Vec<&Node> = func.body.body.iter().collect();
        let captured = free_locals(&body_nodes, &self.locals);
        if func.captures.is_empty() {
            // Implicit captures: celled handles are copyable by
            // construction; everything else must be a Copy value.
            let implicit: Vec<Symbol> = captured
                .iter()
                .filter(|symbol| {
                    self.locals
                        .get(symbol)
                        .is_none_or(|local| !self.cell_handles.contains(local))
                })
                .copied()
                .collect();
            self.check_captures(&implicit, func.body.span)?;
        } else {
            self.check_capture_list(func, &captured)?;
        }
        // Lexical capability capture: the closure carries its creation
        // site's handler for each user effect in its row.
        let effects = self.closure_effects(ty);
        let (env, inherited) = self.capture_env(&captured, &effects)?;

        let id = self.program_builder.reserve(&func.name.name_str());
        let mut fx = FunctionBuilder::new(self.program_builder, 0, self.program);
        fx.subst = self.subst.clone();
        let (celled, nested_refs, use_counts) = cell_scan(&body_nodes);
        fx.celled = celled;
        fx.nested_refs = nested_refs;
        fx.use_counts = use_counts;
        let arity = u16::try_from(func.params.len())
            .map_err(|_| BackendError::new("too many parameters".into(), func.body.span))?;
        fx.next_local = arity;
        for (ix, param) in func.params.iter().enumerate() {
            let local = u16::try_from(ix).unwrap_or_default();
            if let Some(ty) = &param.ty {
                let ty = fx.resolved(ty);
                // `mut` (exclusive-borrow) parameters return their evolved
                // values for the caller's writeback, same as direct calls.
                if matches!(ty, Ty::Borrow(Perm::Exclusive, _)) {
                    fx.writeback_params.push(local);
                }
                fx.check_copy(&ty, func.body.span)?;
                fx.own_local(local, &ty);
            }
            if let Name::Resolved(symbol, _) = &param.name {
                fx.locals.insert(*symbol, local);
            }
        }
        fx.cell_celled_params(&func.params);
        bind_env(
            &self.locals,
            &self.cell_handles,
            &mut fx,
            &captured,
            &inherited,
            &effects,
        );
        let value = fx.compile_block(&func.body)?;
        let (n_locals, blocks) = fx.finish(value)?;
        self.program_builder.functions[id] = Function {
            name: func.name.name_str(),
            arity,
            n_locals,
            blocks,
        };

        let dest = self.fresh_local();
        self.push(Inst::MakeClosure {
            dest,
            func: id,
            env,
        });
        Ok(Operand::Local(dest))
    }

    /// A `Type(args…)` construction: build the fresh value and, when the
    /// type declares an explicit initializer, run its body with the fresh
    /// value as `self`. A resolver-synthesized memberwise initializer has
    /// no body: the record builds directly from the arguments in field
    /// order.
    fn compile_construction(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        args: &[crate::typed_ast::CallArg],
        subst: Vec<(Symbol, Ty)>,
    ) -> Result<Operand, BackendError> {
        let module = self.program_builder.programs[self.program].module;
        // Under an existential coercion the node's type is the coercion
        // target; the construction builds the concrete payload.
        let ty = match &expr.existential_pack {
            Some(pack) => self.resolved(&pack.payload),
            None => self.resolved(&expr.ty),
        };
        let Ty::Nominal(struct_symbol, _) = &ty else {
            return Err(BackendError::unsupported(
                "constructing this type is not supported yet".into(),
                expr.span,
            ));
        };
        let struct_symbol = canonical(*struct_symbol, module);
        let Some((def, _)) = self.program_builder.struct_def(struct_symbol) else {
            return Err(BackendError::unsupported(
                "constructing this type is not supported yet".into(),
                expr.span,
            ));
        };
        let field_count = def.fields.len();
        // The application's type arguments bind the struct's parameters
        // for the initializer body.
        let mut subst = subst;
        if let Ty::Nominal(_, type_args) = &ty {
            for (param, arg) in def.params.iter().zip(type_args) {
                subst.push((param.symbol, arg.clone()));
            }
        }

        // The frontend picked the initializer directly, or — constructing
        // through a protocol's init requirement — via the conformance;
        // dereference its witness table for the implementation.
        let init =
            match &callee.member_resolution {
                Some(crate::types::output::MemberResolution::Direct(init)) => {
                    Some(canonical(*init, module))
                }
                Some(crate::types::output::MemberResolution::ViaConformance {
                    witness,
                    substitution,
                    ..
                }) => {
                    subst.extend(substitution.iter().map(|(symbol, ty)| {
                        (
                            canonical(*symbol, module),
                            self.resolved(&canonical_ty(ty, module)),
                        )
                    }));
                    Some(canonical(*witness, module))
                }
                Some(crate::types::output::MemberResolution::ViaRequirement {
                    protocol, ..
                }) => {
                    // Deferred selection: the constructed type was rigid at
                    // typing; the instance substitution has made it
                    // concrete, so the shared selector's answer is forced.
                    let protocol = crate::types::ty::ProtocolRef {
                        protocol: canonical(protocol.protocol, module),
                        args: protocol
                            .args
                            .iter()
                            .map(|arg| self.resolved(arg))
                            .collect(),
                    };
                    let label = crate::label::Label::Named("init".into());
                    let Some((implementation, row_subst)) = self
                        .program_builder
                        .conformance_witness(&ty, &protocol, &label)
                    else {
                        return Err(BackendError::new(
                            "protocol construction without a selectable conformance".into(),
                            callee.span,
                        ));
                    };
                    subst.extend(row_subst);
                    Some(implementation)
                }
                None => None,
            };

        let mut operands = Vec::new();
        let mut operand_tys = Vec::new();
        for arg in args {
            let operand = self.compile_expr(&arg.value)?;
            operand_tys.push(self.resolved(&arg.value.ty));
            operands.push(operand);
        }

        if def.heap {
            // A `'heap` object allocates its own region; handle-carrying
            // fields store through ObjectSet so their regions merge, and
            // the stored claim retires (containment replaces it).
            // An explicit initializer runs over the fresh object as
            // `self`, mirroring the value path's fresh-record call.
            if let Some(init) = init
                && let Some(callable) = self.program_builder.callables.get(&init).copied()
            {
                if let CallableBody::Init { params, .. } = callable.body {
                    for ((operand, operand_ty), param) in operands
                        .iter()
                        .zip(operand_tys.iter())
                        .zip(params.iter().skip(1))
                    {
                        // An explicit init's borrow param genuinely
                        // borrows: the body decides what to store, and
                        // its own field assignments donate as needed.
                        let borrowed = param
                            .ty
                            .as_ref()
                            .is_some_and(|param_ty| matches!(param_ty, Ty::Borrow(_, _)));
                        if !borrowed {
                            self.consume_into(*operand, operand_ty, expr.span)?;
                        }
                    }
                }
                let obj = self.fresh_local();
                let placeholders = vec![Operand::Const(Constant::Unit); field_count];
                self.push(Inst::ObjectNew {
                    dest: obj,
                    args: placeholders,
                });
                if let Some(func) = self.program_builder.heap_teardown(&ty)? {
                    let thunk = self.fresh_local();
                    self.push(Inst::MakeClosure {
                        dest: thunk,
                        func,
                        env: Vec::new(),
                    });
                    self.push(Inst::SetFinalizer {
                        obj: Operand::Local(obj),
                        closure: Operand::Local(thunk),
                    });
                }
                let mut call_args = vec![Operand::Local(obj)];
                call_args.extend(operands);
                let func = self.program_builder.demand(init, subst, expr.span)?;
                self.program_builder
                    .writeback_expectations
                    .push((func, 0, expr.span));
                self.append_witness_args(func, &mut call_args, expr.span)?;
                let dest = self.fresh_local();
                self.push_call(dest, func, call_args);
                self.produce_temp(dest, &ty);
                return Ok(Operand::Local(dest));
            }
            if operands.len() != field_count {
                return Err(BackendError::new(
                    "memberwise 'heap construction with a field-count mismatch".into(),
                    expr.span,
                ));
            }
            let dest = self.fresh_local();
            let placeholders = vec![Operand::Const(Constant::Unit); field_count];
            self.push(Inst::ObjectNew {
                dest,
                args: placeholders,
            });
            // The finalizer runs as the region tears the object down:
            // the Deinit hook, then buffer-field frees (arity 1,
            // receiving the object as `self`).
            if let Some(func) = self.program_builder.heap_teardown(&ty)? {
                let thunk = self.fresh_local();
                self.push(Inst::MakeClosure {
                    dest: thunk,
                    func,
                    env: Vec::new(),
                });
                self.push(Inst::SetFinalizer {
                    obj: Operand::Local(dest),
                    closure: Operand::Local(thunk),
                });
            }
            for operand in &operands {
                self.consume_operand(*operand);
            }
            for (index, (operand, operand_ty)) in operands.iter().zip(&operand_tys).enumerate() {
                let index = u16::try_from(index).unwrap_or_default();
                self.push(Inst::ObjectSet {
                    obj: Operand::Local(dest),
                    src: *operand,
                    index,
                });
                if contains_object(self.program_builder, operand_ty) {
                    self.push(Inst::RegionRelease { src: *operand });
                }
            }
            self.produce_temp(dest, &ty);
            return Ok(Operand::Local(dest));
        }

        let Some(init) = init else {
            return Err(BackendError::new(
                "construction without a frontend-selected initializer".into(),
                callee.span,
            ));
        };

        let callable = self.program_builder.callables.get(&init).copied();
        // The resolver-synthesized memberwise init assigns each argument
        // to its field and returns `self` — running it as a call costs a
        // frame, one SetField per field, and a defeated copy-on-write per
        // SetField (the blank record is aliased across the caller and
        // init frames, so it is never unique). Build the record directly
        // instead; the synthesized body carries `Span::SYNTHESIZED`, and
        // the arity guard keeps any init with default-valued fields (or
        // a user body) on the call path. Memberwise parameters all
        // consume (ADR 0018), matching the direct path's ownership.
        let synthesized_memberwise = !def.heap
            && callable.is_some_and(|callable| {
                matches!(callable.body, CallableBody::Init { params, body }
                    if body.span == Span::SYNTHESIZED
                        && params.len() == field_count + 1
                        && operands.len() == field_count)
            });

        if let Some(callable) = callable
            && !synthesized_memberwise
        {
            // Explicit initializer: consume per the declared parameter
            // modes, then pass a fresh record as `self`. The init's
            // parameter list includes `self`, so arguments align from 1.
            if let CallableBody::Init { params, .. } = callable.body {
                let tys = operand_tys.clone();
                for ((operand, operand_ty), param) in
                    operands.iter().zip(tys.iter()).zip(params.iter().skip(1))
                {
                    // An explicit init's borrow param genuinely
                    // borrows: the body decides what to store, and its
                    // own field assignments donate as needed.
                    let borrowed = param
                        .ty
                        .as_ref()
                        .is_some_and(|param_ty| matches!(param_ty, Ty::Borrow(_, _)));
                    if !borrowed {
                        // Like a call argument: an operand this frame
                        // does not own (a field read) donates a
                        // reference by retaining.
                        self.consume_into(*operand, operand_ty, expr.span)?;
                    }
                }
            }
            let fresh = self.fresh_local();
            self.push(Inst::Record {
                dest: fresh,
                struct_symbol,
                args: vec![Operand::Const(Constant::Unit); field_count],
            });
            let mut call_args = vec![Operand::Local(fresh)];
            call_args.extend(operands.iter().copied());
            let func = self.program_builder.demand(init, subst, expr.span)?;
            // Constructions never unpack writeback tuples; the validator
            // turns a `mut`-parameter initializer into a compile error.
            self.program_builder
                .writeback_expectations
                .push((func, 0, expr.span));
            self.append_witness_args(func, &mut call_args, expr.span)?;
            let dest = self.fresh_local();
            self.push_call(dest, func, call_args);
            // The construction inherits any argument's provenance.
            for operand in &operands {
                self.propagate_view(Operand::Local(dest), *operand);
            }
            self.produce_temp(dest, &ty);
            Ok(Operand::Local(dest))
        } else {
            // Memberwise: arguments are the fields in declaration order.
            if operands.len() != field_count {
                return Err(BackendError::new(
                    "memberwise construction with a field-count mismatch".into(),
                    expr.span,
                ));
            }
            let tys = operand_tys.clone();
            // Consume with each declared field type: a borrow-typed
            // slot donates a reference to the inner type (owning
            // stored views); view constructions consume like any
            // other struct.
            let field_tys = self
                .program_builder
                .field_types(struct_symbol, head_args(&ty));
            for (index, (operand, operand_ty)) in operands.iter().zip(tys.iter()).enumerate() {
                let dest_ty = field_tys
                    .as_ref()
                    .and_then(|fields| fields.get(index))
                    .cloned()
                    .map(strip_borrows)
                    .unwrap_or_else(|| operand_ty.clone());
                self.consume_into(*operand, &dest_ty, expr.span)?;
            }
            let dest = self.fresh_local();
            for operand in &operands {
                self.propagate_view(Operand::Local(dest), *operand);
            }
            self.push(Inst::Record {
                dest,
                struct_symbol,
                args: operands,
            });
            self.produce_temp(dest, &ty);
            Ok(Operand::Local(dest))
        }
    }

    /// Trusted scalar inline-IR bodies from core sources (ADR 0032's
    /// target-neutral scalar intrinsics).
    fn compile_inline_ir(
        &mut self,
        expr: &Expr,
        instruction: &crate::typed_ast::InlineIRInstruction,
    ) -> Result<Operand, BackendError> {
        use InlineIRInstructionKind as K;

        let dest = self.fresh_local();
        match &instruction.kind {
            K::Alloc { ty, count, .. } => {
                let element = self.annotation_mem_ty(ty, expr.span)?;
                let count = self.ir_value(instruction, count, expr.span)?;
                let bytes = if element.size() == 1 {
                    count
                } else {
                    let scaled = self.fresh_local();
                    self.push(Inst::Scalar {
                        dest: scaled,
                        op: ScalarOp::IntMul,
                        a: count,
                        b: Some(Operand::Const(Constant::Int(i64::from(element.size())))),
                    });
                    Operand::Local(scaled)
                };
                self.push(Inst::Alloc { dest, bytes });
                return Ok(Operand::Local(dest));
            }
            K::Free { ptr } => {
                let ptr = self.ir_value(instruction, ptr, expr.span)?;
                self.push(Inst::Free { src: ptr });
                return Ok(Operand::Const(Constant::Unit));
            }
            K::Retain { ty, value } => {
                // Structural: one reference per refcounted buffer the value
                // owns (RawPtr fields are buffers).
                let element = self.annotation_value_ty(ty, expr.span)?;
                let value = self.ir_value(instruction, value, expr.span)?;
                self.retain_value(value, &element, expr.span)?;
                return Ok(Operand::Const(Constant::Unit));
            }
            K::IsUnique { ptr, .. } => {
                let ptr = self.ir_value(instruction, ptr, expr.span)?;
                self.push(Inst::IsUnique { dest, src: ptr });
                return Ok(Operand::Local(dest));
            }
            K::Load { ty, addr, .. } => {
                let kind = self.annotation_mem_ty(ty, expr.span)?;
                let ptr = self.ir_value(instruction, addr, expr.span)?;
                self.push(Inst::Load { dest, ptr, kind });
                return Ok(Operand::Local(dest));
            }
            K::Store { value, ty, addr } => {
                let kind = self.annotation_mem_ty(ty, expr.span)?;
                let src = self.ir_value(instruction, value, expr.span)?;
                let ptr = self.ir_value(instruction, addr, expr.span)?;
                // The write donates the value to memory: its previous
                // owner (usually `_store`'s consumed parameter) must not
                // also drop it.
                self.consume_operand(src);
                self.push(Inst::Store { ptr, src, kind });
                return Ok(Operand::Const(Constant::Unit));
            }
            K::Swap { ty, a, b } => {
                // Exchange two memory slots: two loads, two crossed
                // stores. Ownership is unchanged — each slot still owns
                // exactly one value.
                let kind = self.annotation_mem_ty(ty, expr.span)?;
                let first = self.ir_value(instruction, a, expr.span)?;
                let second = self.ir_value(instruction, b, expr.span)?;
                let from_first = self.fresh_local();
                self.push(Inst::Load {
                    dest: from_first,
                    ptr: first,
                    kind,
                });
                let from_second = self.fresh_local();
                self.push(Inst::Load {
                    dest: from_second,
                    ptr: second,
                    kind,
                });
                self.push(Inst::Store {
                    ptr: first,
                    src: Operand::Local(from_second),
                    kind,
                });
                self.push(Inst::Store {
                    ptr: second,
                    src: Operand::Local(from_first),
                    kind,
                });
                return Ok(Operand::Const(Constant::Unit));
            }
            K::Take { ty, value, .. } => {
                // The place invalidation is MIR bookkeeping; the value
                // itself just moves — and the result OWNS it (a binding
                // must consume, not retain, this temporary).
                let value = self.ir_value(instruction, value, expr.span)?;
                self.push(Inst::Copy { dest, src: value });
                let owned = self.annotation_value_ty(ty, expr.span)?;
                self.produce_temp(dest, &owned);
                return Ok(Operand::Local(dest));
            }
            K::Copy {
                from, to, length, ..
            } => {
                let from = self.ir_value(instruction, from, expr.span)?;
                let to = self.ir_value(instruction, to, expr.span)?;
                let len = self.ir_value(instruction, length, expr.span)?;
                self.push(Inst::MemCopy { from, to, len });
                return Ok(Operand::Const(Constant::Unit));
            }
            K::InlineGet { array, index, .. } => {
                let array = self.ir_value(instruction, array, expr.span)?;
                let index = self.ir_value(instruction, index, expr.span)?;
                self.push(Inst::GetElement {
                    dest,
                    src: array,
                    index,
                });
                return Ok(Operand::Local(dest));
            }
            K::Gep {
                ty,
                addr,
                offset_index,
                ..
            } => {
                let element = self.annotation_mem_ty(ty, expr.span)?;
                let ptr = self.ir_value(instruction, addr, expr.span)?;
                let offset = self.ir_value(instruction, offset_index, expr.span)?;
                self.push(Inst::PtrAdd {
                    dest,
                    ptr,
                    offset,
                    size: element.size(),
                });
                return Ok(Operand::Local(dest));
            }
            K::IoWrite { fd, buf, count, .. } => {
                let a = self.ir_value(instruction, fd, expr.span)?;
                let b = self.ir_value(instruction, buf, expr.span)?;
                let c = self.ir_value(instruction, count, expr.span)?;
                self.push(Inst::Io {
                    dest,
                    op: 1,
                    a,
                    b,
                    c,
                });
                return Ok(Operand::Local(dest));
            }
            K::Add { ty, a, b, .. } if ty.simple_name() == "RawPtr" => {
                let ptr = self.ir_value(instruction, a, expr.span)?;
                let offset = self.ir_value(instruction, b, expr.span)?;
                self.push(Inst::PtrAdd {
                    dest,
                    ptr,
                    offset,
                    size: 1,
                });
                return Ok(Operand::Local(dest));
            }
            _ => {}
        }
        let (op, a, b) = match &instruction.kind {
            K::Add { ty, a, b, .. } => (
                self.arith_op(&ty.simple_name(), Arith::Add, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                Some(self.ir_value(instruction, b, expr.span)?),
            ),
            K::Sub { ty, a, b, .. } => (
                self.arith_op(&ty.simple_name(), Arith::Sub, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                Some(self.ir_value(instruction, b, expr.span)?),
            ),
            K::Mul { ty, a, b, .. } => (
                self.arith_op(&ty.simple_name(), Arith::Mul, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                Some(self.ir_value(instruction, b, expr.span)?),
            ),
            K::Div { ty, a, b, .. } => (
                self.arith_op(&ty.simple_name(), Arith::Div, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                Some(self.ir_value(instruction, b, expr.span)?),
            ),
            K::And { ty, a, b, .. } => (
                self.bit_op(&ty.simple_name(), Bit::And, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                Some(self.ir_value(instruction, b, expr.span)?),
            ),
            K::Or { ty, a, b, .. } => (
                self.bit_op(&ty.simple_name(), Bit::Or, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                Some(self.ir_value(instruction, b, expr.span)?),
            ),
            K::Xor { ty, a, b, .. } => (
                self.bit_op(&ty.simple_name(), Bit::Xor, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                Some(self.ir_value(instruction, b, expr.span)?),
            ),
            K::Shl { ty, a, b, .. } => (
                self.bit_op(&ty.simple_name(), Bit::Shl, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                Some(self.ir_value(instruction, b, expr.span)?),
            ),
            K::Shr { ty, a, b, .. } => (
                self.bit_op(&ty.simple_name(), Bit::Shr, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                Some(self.ir_value(instruction, b, expr.span)?),
            ),
            K::Not { ty, a, .. } => (
                self.bit_op(&ty.simple_name(), Bit::Not, expr.span)?,
                self.ir_value(instruction, a, expr.span)?,
                None,
            ),
            K::Cmp {
                ty, lhs, rhs, op, ..
            } => {
                let kind = match op {
                    TokenKind::EqualsEquals => CmpKind::Eq,
                    TokenKind::BangEquals => CmpKind::Ne,
                    TokenKind::Less => CmpKind::Lt,
                    TokenKind::LessEquals => CmpKind::Le,
                    TokenKind::Greater => CmpKind::Gt,
                    TokenKind::GreaterEquals => CmpKind::Ge,
                    _ => {
                        return Err(BackendError::new(
                            "unsupported comparison operator in inline IR".into(),
                            expr.span,
                        ));
                    }
                };
                let op = match ty.simple_name().as_str() {
                    "Int" => ScalarOp::IntCmp(kind),
                    "Float" => ScalarOp::FloatCmp(kind),
                    "Byte" => ScalarOp::ByteCmp(kind),
                    "Bool" if matches!(kind, CmpKind::Eq | CmpKind::Ne) => ScalarOp::BoolCmp(kind),
                    other => {
                        return Err(BackendError::unsupported(
                            format!("inline IR comparisons on `{other}` are not supported yet"),
                            expr.span,
                        ));
                    }
                };
                (
                    op,
                    self.ir_value(instruction, lhs, expr.span)?,
                    Some(self.ir_value(instruction, rhs, expr.span)?),
                )
            }
            K::Trunc { val, .. } => (
                ScalarOp::FloatToIntTrunc,
                self.ir_value(instruction, val, expr.span)?,
                None,
            ),
            K::IntToFloat { val, .. } => (
                ScalarOp::IntToFloat,
                self.ir_value(instruction, val, expr.span)?,
                None,
            ),
            K::ByteToInt { val, .. } => (
                ScalarOp::ByteToInt,
                self.ir_value(instruction, val, expr.span)?,
                None,
            ),
            other => {
                return Err(BackendError::unsupported(
                    format!("inline IR operation `{other:?}` is not supported yet"),
                    expr.span,
                ));
            }
        };

        self.push(Inst::Scalar { dest, op, a, b });
        Ok(Operand::Local(dest))
    }

    fn arith_op(&self, ty: &str, arith: Arith, span: Span) -> Result<ScalarOp, BackendError> {
        let op = match (ty, arith) {
            ("Int", Arith::Add) => ScalarOp::IntAdd,
            ("Int", Arith::Sub) => ScalarOp::IntSub,
            ("Int", Arith::Mul) => ScalarOp::IntMul,
            ("Int", Arith::Div) => ScalarOp::IntDiv,
            ("Float", Arith::Add) => ScalarOp::FloatAdd,
            ("Float", Arith::Sub) => ScalarOp::FloatSub,
            ("Float", Arith::Mul) => ScalarOp::FloatMul,
            ("Float", Arith::Div) => ScalarOp::FloatDiv,
            _ => {
                return Err(BackendError::unsupported(
                    format!("inline IR arithmetic on `{ty}` is not supported yet"),
                    span,
                ));
            }
        };
        Ok(op)
    }

    fn bit_op(&self, ty: &str, bit: Bit, span: Span) -> Result<ScalarOp, BackendError> {
        let op = match (ty, bit) {
            ("Int", Bit::And) => ScalarOp::IntAnd,
            ("Int", Bit::Or) => ScalarOp::IntOr,
            ("Int", Bit::Xor) => ScalarOp::IntXor,
            ("Int", Bit::Shl) => ScalarOp::IntShl,
            ("Int", Bit::Shr) => ScalarOp::IntShr,
            ("Int", Bit::Not) => ScalarOp::IntNot,
            ("Byte", Bit::And) => ScalarOp::ByteAnd,
            ("Byte", Bit::Or) => ScalarOp::ByteOr,
            ("Byte", Bit::Xor) => ScalarOp::ByteXor,
            ("Byte", Bit::Shl) => ScalarOp::ByteShl,
            ("Byte", Bit::Shr) => ScalarOp::ByteShr,
            ("Byte", Bit::Not) => ScalarOp::ByteNot,
            _ => {
                return Err(BackendError::unsupported(
                    format!("inline IR bitwise operation on `{ty}` is not supported yet"),
                    span,
                ));
            }
        };
        Ok(op)
    }

    /// Inline-IR operands: `%N` is the N-th parameter (with the receiver at
    /// `%0` in methods), `$N` is a bound sub-expression, immediates carry
    /// their value.
    fn ir_value(
        &mut self,
        instruction: &crate::typed_ast::InlineIRInstruction,
        value: &IrValue,
        span: Span,
    ) -> Result<Operand, BackendError> {
        match value {
            IrValue::Reg(index) => {
                let local = u16::try_from(*index).map_err(|_| {
                    BackendError::new("inline IR register out of range".into(), span)
                })?;
                Ok(Operand::Local(local))
            }
            IrValue::Bind(index) => {
                let Some(bound) = instruction.binds.get(*index) else {
                    return Err(BackendError::new(
                        "inline IR bind out of range".into(),
                        span,
                    ));
                };
                self.compile_expr(bound)
            }
            IrValue::Int(value) => Ok(Operand::Const(Constant::Int(*value))),
            IrValue::Float(value) => Ok(Operand::Const(Constant::Float(*value))),
            IrValue::Bool(value) => Ok(Operand::Const(Constant::Bool(*value))),
            IrValue::Void => Ok(Operand::Const(Constant::Unit)),
            _ => Err(BackendError::unsupported(
                "this inline IR operand is not supported yet".into(),
                span,
            )),
        }
    }
}

#[derive(Clone, Copy)]
enum Arith {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Copy)]
enum Bit {
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Not,
}

trait SimpleName {
    fn simple_name(&self) -> String;
}

impl SimpleName for crate::node_kinds::type_annotation::TypeAnnotation {
    fn simple_name(&self) -> String {
        use crate::node_kinds::type_annotation::TypeAnnotationKind;
        match &self.kind {
            TypeAnnotationKind::Nominal { name, .. } => name.name_str(),
            _ => String::new(),
        }
    }
}
