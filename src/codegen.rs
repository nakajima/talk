//! Public code-generation input produced from the compiler's private MIR.
//!
//! External backend crates consume this model without depending on private
//! compiler modules. The model describes execution semantics, not a target.

use std::collections::HashMap;
use std::hash::Hash;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpKind {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

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
pub enum Inst<S> {
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
        unwind: Option<BlockId>,
    },
    Tuple {
        dest: LocalId,
        args: Vec<Operand>,
    },
    TupleGet {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    Variant {
        dest: LocalId,
        enum_symbol: S,
        tag: u16,
        args: Vec<Operand>,
    },
    GetTag {
        dest: LocalId,
        src: Operand,
    },
    GetPayload {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    Record {
        dest: LocalId,
        struct_symbol: S,
        args: Vec<Operand>,
    },
    GetField {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    GetElement {
        dest: LocalId,
        src: Operand,
        index: Operand,
    },
    SetField {
        rec: LocalId,
        src: Operand,
        index: u16,
    },
    StringLit {
        dest: LocalId,
        bytes: Vec<u8>,
    },
    BytesLit {
        dest: LocalId,
        bytes: Vec<u8>,
    },
    Alloc {
        dest: LocalId,
        bytes: Operand,
    },
    Free {
        src: Operand,
    },
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
    PtrAdd {
        dest: LocalId,
        ptr: Operand,
        offset: Operand,
        size: u32,
    },
    Io {
        dest: LocalId,
        op: u8,
        a: Operand,
        b: Operand,
        c: Operand,
    },
    ObjectNew {
        dest: LocalId,
        args: Vec<Operand>,
    },
    ObjectGet {
        dest: LocalId,
        src: Operand,
        index: u16,
    },
    ObjectSet {
        obj: Operand,
        src: Operand,
        index: u16,
    },
    RegionAcquire {
        src: Operand,
    },
    RegionRelease {
        src: Operand,
    },
    MakeClosure {
        dest: LocalId,
        func: FuncId,
        env: Vec<Operand>,
    },
    SetFinalizer {
        obj: Operand,
        closure: Operand,
    },
    CellNew {
        dest: LocalId,
        init: Operand,
    },
    CellGet {
        dest: LocalId,
        cell: Operand,
    },
    CellSet {
        cell: Operand,
        src: Operand,
    },
    CallIndirect {
        dest: LocalId,
        callee: Operand,
        args: Vec<Operand>,
        unwind: Option<BlockId>,
    },
    EnvGet {
        dest: LocalId,
        index: u16,
    },
    MakeCont {
        dest: LocalId,
    },
    PushHandler {
        effect: S,
        clause: Operand,
        cont: Operand,
    },
    FindHandler {
        clause: LocalId,
        cont: LocalId,
        index: LocalId,
        effect: S,
    },
    GetFloor {
        dest: LocalId,
    },
    SetFloor {
        src: Operand,
    },
    GlobalLoad {
        dest: LocalId,
        global: u32,
    },
    GlobalStore {
        global: u32,
        src: Operand,
    },
    ExistentialPack {
        dest: LocalId,
        protocol: S,
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
    AbortTo {
        cont: Operand,
        value: Operand,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemTy {
    Byte,
    I64,
    F64,
    Bool,
    Ptr,
    Boxed,
}

#[derive(Clone, Debug)]
pub enum Term {
    Goto(BlockId, Vec<Operand>),
    Branch {
        cond: Operand,
        then_block: BlockId,
        else_block: BlockId,
    },
    Switch {
        tag: Operand,
        targets: Vec<BlockId>,
        default: BlockId,
    },
    Return(Operand),
    Trap(String),
    UnwindRet,
}

#[derive(Clone, Debug, Default)]
pub struct BlockData<S> {
    pub params: Vec<LocalId>,
    pub insts: Vec<Inst<S>>,
    pub term: Option<Term>,
}

#[derive(Clone, Debug)]
pub struct Function<S> {
    pub name: String,
    pub arity: u16,
    pub n_locals: u16,
    pub blocks: Vec<BlockData<S>>,
}

#[derive(Clone, Debug)]
pub struct Program<S> {
    pub functions: Vec<Function<S>>,
    pub entry: FuncId,
    pub global_slots: u32,
}

#[derive(Clone, Copy, Debug)]
pub enum TypeKind {
    Record,
    Enum,
    String,
}

#[derive(Clone, Debug)]
pub struct DisplayNames<S> {
    pub entries: HashMap<S, (String, TypeKind, Vec<String>)>,
}

impl<S> Default for DisplayNames<S> {
    fn default() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }
}

pub struct Compilation<S> {
    pub program: Program<S>,
    pub display_names: DisplayNames<S>,
    pub string_symbol: S,
    pub storage_symbol: S,
}

/// Native runtime source shared by external ahead-of-time backends.
pub fn native_runtime_c() -> &'static str {
    include_str!("backend/c_prelude.c")
}

impl<S: Eq + Hash> DisplayNames<S> {
    pub fn insert(&mut self, symbol: S, name: String, kind: TypeKind, members: Vec<String>) {
        self.entries.insert(symbol, (name, kind, members));
    }
}
