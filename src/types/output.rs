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

/// The checked contract of one effect site — a perform or a handler
/// (ADR 0038). Declared parameter types keep rigid generics as
/// `Ty::Param`; the type-generic list fixes the hidden witness-block
/// layout both sides must agree on. Lowering never reloads effect
/// signatures.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct EffectContract {
    pub params: Vec<Ty>,
    pub type_generics: Vec<Symbol>,
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

pub(crate) fn stored_field_symbol(
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

#[derive(Clone, Default, Debug, serde::Serialize, serde::Deserialize)]
pub struct TypeOutput {
    /// The module this check ran under — tooling's member-accessibility
    /// viewer (ADR 0042) pairs it with the cursor's file.
    pub module_id: crate::compiling::module::ModuleId,
    /// This module's slice of the type catalog (exported with the module).
    pub catalog: crate::types::catalog::TypeCatalog,
    /// Zonked type of every expression and parameter node. The typed-program
    /// builder bakes these types onto its tree, while editor analysis reads
    /// this map against the source-faithful AST. Binder nodes use
    /// [`Self::binder_ty`] instead.
    pub node_types: FxHashMap<NodeID, Ty>,
    /// Finished scheme for every top-level binder (monomorphic binders get
    /// empty-parameter schemes).
    pub schemes: FxHashMap<Symbol, Scheme>,
    /// Per-use-site instantiation of a scheme's parameters, preserved as a
    /// checked semantic fact on TypedProgram.
    pub instantiations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    /// Source origin of each checker-inferred generic parameter. This is
    /// presentation provenance, not part of type identity.
    #[serde(default)]
    pub inferred_param_origins: FxHashMap<Symbol, NodeID>,
    /// The one concrete assignment a stored rank-N closure compiles at,
    /// computed at finalize from its projections — baked onto the
    /// field-value node (a func literal or a generic reference) for
    /// lowering. Absent when the closure stays rigid.
    pub field_specializations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    /// A projection whose stored closure compiled rigidly: the rigid
    /// parameters and this use's arguments, in scheme order — the
    /// hidden witness-block layout the call appends (a concrete
    /// argument's witnesses are materialized; a rigid one forwards the
    /// caller's own).
    pub witness_layouts: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    pub member_resolutions: FxHashMap<NodeID, MemberResolution>,
    /// The selected callable symbol per statically resolved call node
    /// (ADR 0041).
    pub selected_callables: FxHashMap<NodeID, Symbol>,
    /// Signed 64-bit values or explicit recovery for every integer literal
    /// expression and pattern (ledger row LIT-01).
    pub integer_literals: FxHashMap<NodeID, CheckedIntegerLiteral>,
    /// Per-`for`-statement iteration plans (keyed by the statement node).
    /// Consumed only by the typed-tree build, which elaborates the loop
    /// into ordinary nodes at the plan's ids.
    pub for_plans: FxHashMap<NodeID, ForPlan>,
    /// Checked two-variant match expansions for postfix `?` and `!`.
    pub propagation_plans: FxHashMap<NodeID, PropagationPlan>,
    /// Per-file low-water mark of the checker's descending id mint: the
    /// typed-tree build mints its elaborated-node ids below this.
    pub synthetic_floors: FxHashMap<crate::node_id::FileID, u32>,
    /// Argument nodes where a borrowed value satisfies an owned CheapClone
    /// parameter through an explicit clone coercion.
    pub coerce_clones: rustc_hash::FxHashSet<NodeID>,
    /// Finalized types of monomorphic local binders, including pattern binds.
    /// Read them through [`Self::binder_ty`].
    pub local_tys: FxHashMap<Symbol, Ty>,
    /// Expression nodes implicitly packed into an existential expected type.
    pub existential_packs: FxHashMap<NodeID, ExistentialPack>,
    /// Checked inline-IR operation per `#_ir` expression (ADR 0038). The
    /// typed-tree build bakes these onto the tree; lowering never
    /// interprets parser instructions.
    pub checked_ir: FxHashMap<NodeID, CheckedIrKind>,
    /// Checked effect contract per perform expression and handler
    /// statement (ADR 0038), baked onto the typed tree.
    pub effect_contracts: FxHashMap<NodeID, EffectContract>,
    /// Each checked pattern occurrence's finalized type (pre-view:
    /// binders keep their borrows), record-field slots included, baked
    /// onto the typed tree (ADR 0038).
    pub pattern_tys: FxHashMap<NodeID, Ty>,
    /// Per struct pattern: one slot per stored field in declaration
    /// order — the instantiated field type and the covering sub-pattern
    /// node (ADR 0038), baked onto the typed tree as indices.
    pub struct_pattern_slots: FxHashMap<NodeID, Vec<(Ty, Option<NodeID>)>>,
    /// Per record pattern on a closed named row: one slot per row field
    /// in layout order — slot type and covering written field
    /// (ADR 0038). Open or unresolved rows have no entry.
    pub record_pattern_slots: FxHashMap<NodeID, Vec<(Ty, Option<NodeID>)>>,
    /// Imported and local symbol names merged for diagnostics and editor views.
    pub display_names: FxHashMap<Symbol, String>,
}

impl TypeOutput {
    /// The one authority for a local binder's type (parameters and
    /// pattern binds included), keyed by symbol. Binder NODES carry no
    /// `node_types` entry, so there is nothing to fall back to.
    pub fn binder_ty(&self, symbol: Symbol) -> Option<&Ty> {
        self.local_tys.get(&symbol)
    }
}
