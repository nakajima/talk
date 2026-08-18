//! The type checker's outputs: everything later phases consume. The lowerer
//! reads tables (schemes, per-call-site instantiations, member resolutions —
//! the dictionary-or-monomorphization surface of Wadler & Blott, POPL 1989);
//! it never asks the checker questions.

use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;
use crate::node_id::NodeID;
use crate::types::{
    catalog::ConformanceId,
    ty::{ProtocolRef, Scheme, Ty},
};

/// The checker's published plan for one `for` statement: the resolved
/// `iter()`/`next()` call nodes (their member resolutions and
/// instantiations live in the ordinary tables under these ids) and the
/// finished iterator/element types. The typed-tree build consumes the
/// plan, elaborating the loop into ordinary nodes at these ids; nothing
/// downstream of the typed tree sees it.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ForPlan {
    pub iter_callee_id: NodeID,
    pub iter_call_id: NodeID,
    pub next_callee_id: NodeID,
    pub next_call_id: NodeID,
    /// Mut-mode (`for x in mut xs`) extras: the compiler-owned
    /// `_store_current(value)` call and its argument node (the binder read).
    /// Unused for other modes.
    pub mut_store_callee_id: NodeID,
    pub mut_store_call_id: NodeID,
    pub mut_store_arg_id: NodeID,
    pub iterator_ty: Ty,
    pub element_ty: Ty,
    pub next_result_ty: Ty,
    /// The body block's value type: the per-iteration match join discards
    /// it, and the discard must drop droppable tails.
    pub body_ty: Ty,
}

/// Checked expansion of postfix `?` or `!`. The checker builds and checks the
/// ordinary two-arm match once; typed-tree construction substitutes it for the
/// surface node so downstream phases need no postfix-specific form.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct PropagationPlan {
    pub lowered: crate::node_kinds::expr::Expr,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ExistentialPack {
    pub existential: Ty,
    pub payload: Ty,
}

/// A checker-committed implicit conversion at a value crossing: the
/// expression node converts into its slot through the one declared
/// `Into` row. The typed-tree build wraps the node in a synthesized
/// `.into()` member call carrying this resolution; downstream phases see
/// an ordinary call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntoCoercion {
    /// The type the inserted call produces — the slot the value crossed
    /// into.
    pub target: Ty,
    /// How the `.into()` dispatches, committed like any member call's
    /// resolution (finalize upgrades the requirement operation to its
    /// concrete witness exactly as it does for source-written calls).
    pub resolution: MemberResolution,
}

/// The checked contract of one effect site — a perform or a handler
/// (ADR 0038). Declared parameter types keep rigid generics as
/// `Ty::Param`; the type-generic list fixes the hidden witness-block
/// layout both sides must agree on, while the static-generic list keys
/// ordinary whole-program specialization. Lowering never reloads effect
/// signatures.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct EffectContract {
    pub params: Vec<Ty>,
    pub type_generics: Vec<Symbol>,
    #[serde(default)]
    pub static_generics: Vec<Symbol>,
    /// ADR 0068: this `#handle` clause binds the stored resumption as a
    /// final parameter — derived from the clause's binder count, never
    /// declared. Always false on perform-site contracts.
    pub binds_resumption: bool,
    /// ADR 0068: a resumption-binding clause is legal for this effect —
    /// its signature has no generics and no exclusive-borrow (`mut`)
    /// parameters. Perform lowering emits the runtime clause-kind
    /// branch exactly for bindable effects.
    pub bindable: bool,
}

/// A checked inline-IR operation (ADR 0038): canonical operation
/// identity, checked types, and validated operands. Types stay frontend
/// types — a generic annotation substitutes per instance during backend
/// specialization, and memory-kind selection from the substituted type
/// is lowering's representation work. Lowering only emits the
/// corresponding MIR operation; it never interprets parser instructions.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CheckedIrKind {
    /// A scalar computation whose (type, operation) combination the
    /// checker validated.
    Scalar {
        op: IrScalarOp,
        a: IrOperand,
        b: Option<IrOperand>,
    },
    Alloc {
        elem: Ty,
        count: IrOperand,
    },
    Free {
        ptr: IrOperand,
    },
    Retain {
        ty: Ty,
        value: IrOperand,
    },
    IsUnique {
        ptr: IrOperand,
    },
    Load {
        ty: Ty,
        addr: IrOperand,
    },
    Store {
        ty: Ty,
        value: IrOperand,
        addr: IrOperand,
    },
    Swap {
        ty: Ty,
        a: IrOperand,
        b: IrOperand,
    },
    Take {
        ty: Ty,
        value: IrOperand,
    },
    MemCopy {
        from: IrOperand,
        to: IrOperand,
        length: IrOperand,
    },
    InlineGet {
        element: Ty,
        array: IrOperand,
        index: IrOperand,
    },
    Gep {
        elem: Ty,
        addr: IrOperand,
        offset: IrOperand,
    },
    /// A host io operation: `op` indexes the runtime's operation table
    /// and is committed at check time (an integer literal in the IR
    /// text); unused operand slots pass zero.
    Io {
        op: u8,
        a: IrOperand,
        b: IrOperand,
        c: IrOperand,
    },
    /// ADR 0058 task runtime: start a worker running an `(A) -> T`
    /// closure over the transferred `arg`, producing an executor-internal
    /// handle. The argument convention (not capture) keeps the worker
    /// closure environment-free.
    TaskSpawn {
        arg: IrOperand,
        worker: IrOperand,
    },
    /// ADR 0058 task runtime: join a spawned worker and take its
    /// output, whose checked type is `ty`.
    TaskJoin {
        ty: Ty,
        handle: IrOperand,
    },
    /// ADR 0058 task runtime: the host's available parallelism.
    TaskWidth,
    /// ADR 0059: enqueue a transferred value on a channel and wake its
    /// waiter.
    ChanSend {
        handle: IrOperand,
        value: IrOperand,
    },
    /// ADR 0059: take a queued value off a channel (trap when none —
    /// callers gate on `chan_ctl` status first).
    ChanTake {
        ty: Ty,
        handle: IrOperand,
    },
    /// ADR 0059: scalar channel/park control. Ops: 0 status, 1 retain
    /// sender, 2 drop sender, 3 drop receiver, 4 register external wait,
    /// 5 unregister, 6 park, 7 create (handle ignored).
    ChanCtl {
        handle: IrOperand,
        op: IrOperand,
    },
    /// ADR 0064: resume a stored one-shot resumption with a value; the
    /// checked type is the handled extent's answer, transferred to the
    /// resumer when the extent finishes.
    Resume {
        ty: Ty,
        cont: IrOperand,
        value: IrOperand,
    },
    /// ADR 0064: cancel a stored resumption, unwinding its captured
    /// frames through their cleanup entries.
    Cancel { cont: IrOperand },
}

/// The scalar operations inline IR may perform, with their operand
/// scalar committed — every combination here is checker-validated.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum IrScalarOp {
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
    IntCmp(IrCmp),
    FloatCmp(IrCmp),
    ByteCmp(IrCmp),
    /// Only equality and inequality — validated at the perform site.
    BoolCmp(IrCmp),
    /// Allocation identity for opaque snapshot-bound indices.
    PtrCmp(IrCmp),
    FloatToIntTrunc,
    IntToFloat,
    ByteToInt,
    IntToByte,
    /// `add RawPtr ptr offset`: byte-wise pointer arithmetic.
    PtrAdd,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum IrCmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// A validated inline-IR operand: `%N` names the enclosing function's
/// N-th parameter, `$N` the N-th bound sub-expression, immediates carry
/// their value. Float equality is bit identity (canonical literals).
#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub enum IrOperand {
    Reg(u16),
    Bind(u16),
    Int(i64),
    Float(f64),
    Bool(bool),
    Void,
}

impl PartialEq for IrOperand {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Reg(a), Self::Reg(b)) | (Self::Bind(a), Self::Bind(b)) => a == b,
            (Self::Int(a), Self::Int(b)) => a == b,
            (Self::Float(a), Self::Float(b)) => a.to_bits() == b.to_bits(),
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::Void, Self::Void) => true,
            _ => false,
        }
    }
}

impl Eq for IrOperand {}

/// How a member access resolved. Concrete conformance dispatch publishes the
/// committed row, witness, and row substitution (ADR 0036's two-point rule:
/// typing commits everything decidable at typing time). A receiver still
/// rigid at finalization stays a requirement operation; the backend resolves
/// it per specialization through the same catalog selector, which coherence
/// makes a forced lookup.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MemberResolution {
    Direct(Symbol),
    ViaConformance {
        row: ConformanceId,
        protocol: ProtocolRef,
        witness: Symbol,
        substitution: Vec<(Symbol, Ty)>,
    },
    ViaRequirement {
        protocol: ProtocolRef,
        requirement: Symbol,
        self_ty: Ty,
    },
}

/// A validated signed 64-bit integer literal, or an explicit recovery for a
/// literal outside the `i64` range (ledger row LIT-01).
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CheckedIntegerLiteral {
    Value(i64),
    Invalid,
}

pub fn stored_field_symbol(
    catalog: &crate::types::catalog::TypeCatalog,
    schemes: &FxHashMap<Symbol, Scheme>,
    resolution: Option<&MemberResolution>,
) -> Option<Symbol> {
    let MemberResolution::Direct(property) = resolution? else {
        return None;
    };
    let in_catalog = catalog.structs.values().any(|info| {
        info.fields
            .values()
            .any(|(field_symbol, _)| field_symbol == property)
    });
    let has_field_scheme = schemes
        .get(property)
        .is_some_and(|scheme| !matches!(scheme.ty, Ty::Func(..)));
    (in_catalog || has_field_scheme).then_some(*property)
}

/// The checker's published program-level facts: everything here is
/// symbol- or module-keyed. Per-occurrence (NodeID-keyed) decisions are
/// NOT published — they travel to the typed-tree build as [`Elaboration`]
/// and live on as tree fields, present by construction (ADR 0057).
#[derive(Clone, Default, Debug, serde::Serialize, serde::Deserialize)]
pub struct TypeOutput {
    /// The module this check ran under — tooling's member-accessibility
    /// viewer (ADR 0042) pairs it with the cursor's file.
    pub module_id: crate::front::module::ModuleId,
    /// This module's slice of the type catalog (exported with the module).
    pub catalog: crate::types::catalog::TypeCatalog,
    /// Finished scheme for every top-level binder (monomorphic binders get
    /// empty-parameter schemes).
    pub schemes: FxHashMap<Symbol, Scheme>,
    /// Source origin of each checker-inferred generic parameter. This is
    /// presentation provenance, not part of type identity.
    #[serde(default)]
    pub inferred_param_origins: FxHashMap<Symbol, NodeID>,
    /// Finalized types of monomorphic local binders, including pattern binds.
    /// Read them through [`Self::binder_ty`].
    pub local_tys: FxHashMap<Symbol, Ty>,
    /// Imported and local symbol names merged for diagnostics and editor views.
    pub display_names: FxHashMap<Symbol, String>,
}

impl TypeOutput {
    /// The one authority for a local binder's type (parameters and
    /// pattern binds included), keyed by symbol. Binder NODES carry no
    /// baked type, so there is nothing to fall back to.
    pub fn binder_ty(&self, symbol: Symbol) -> Option<&Ty> {
        self.local_tys.get(&symbol)
    }
}

/// Per-occurrence elaboration facts: produced by finalize, consumed once
/// by the typed-tree build (which bakes each entry onto its node), and
/// never published — deliberately not serializable, so no later phase can
/// grow a dependency on the tables instead of the tree (ADR 0057 slice 2).
#[derive(Default, Debug)]
pub struct Elaboration {
    /// Zonked type of every expression and parameter node.
    pub node_types: FxHashMap<NodeID, Ty>,
    /// Per-use-site instantiation of a scheme's parameters.
    pub instantiations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    /// The one concrete assignment a stored rank-N closure compiles at,
    /// computed at finalize from its projections. Absent when the
    /// closure stays rigid.
    pub field_specializations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    /// A projection whose stored closure compiled rigidly: the rigid
    /// parameters and this use's arguments, in scheme order — the
    /// hidden witness-block layout the call appends.
    pub witness_layouts: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    pub member_resolutions: FxHashMap<NodeID, MemberResolution>,
    /// The selected callable symbol per statically resolved call node
    /// (ADR 0041).
    pub selected_callables: FxHashMap<NodeID, Symbol>,
    /// Signed 64-bit values or explicit recovery for every integer literal
    /// expression and pattern (ledger row LIT-01).
    pub integer_literals: FxHashMap<NodeID, CheckedIntegerLiteral>,
    /// Per-`for`-statement iteration plans (keyed by the statement node),
    /// elaborated into ordinary nodes at the plan's ids.
    pub for_plans: FxHashMap<NodeID, ForPlan>,
    /// Checked two-variant match expansions for postfix `?` and `!`.
    pub propagation_plans: FxHashMap<NodeID, PropagationPlan>,
    /// Per-file low-water mark of the checker's descending id mint: the
    /// typed-tree build mints its elaborated-node ids below this.
    pub synthetic_floors: FxHashMap<crate::node_id::FileID, u32>,
    /// Argument nodes where a borrowed value satisfies an owned Clone
    /// parameter through an explicit clone coercion (ADR 0054).
    pub coerce_clones: rustc_hash::FxHashSet<NodeID>,
    /// Expression nodes implicitly packed into an existential expected type.
    pub existential_packs: FxHashMap<NodeID, ExistentialPack>,
    /// Expression nodes implicitly converted into their slot through a
    /// declared `Into` row (wrapped in a synthesized `.into()` call).
    pub into_coercions: FxHashMap<NodeID, IntoCoercion>,
    /// Checked inline-IR operation per `#_ir` expression (ADR 0038).
    pub checked_ir: FxHashMap<NodeID, CheckedIrKind>,
    /// Checked effect contract per perform expression and handler
    /// statement (ADR 0038).
    pub effect_contracts: FxHashMap<NodeID, EffectContract>,
    /// Each checked pattern occurrence's finalized type (pre-view:
    /// binders keep their borrows), record-field slots included.
    pub pattern_tys: FxHashMap<NodeID, Ty>,
    /// Per struct pattern: one slot per stored field in declaration
    /// order — the instantiated field type and the covering sub-pattern
    /// node (ADR 0038), baked onto the typed tree as indices.
    pub struct_pattern_slots: FxHashMap<NodeID, Vec<(Ty, Option<NodeID>)>>,
    /// Per record pattern on a closed named row: one slot per row field
    /// in layout order — slot type and covering written field
    /// (ADR 0038). Open or unresolved rows have no entry.
    pub record_pattern_slots: FxHashMap<NodeID, Vec<(Ty, Option<NodeID>)>>,
}
