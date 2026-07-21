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
#[derive(Clone, Debug, PartialEq, Eq)]
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

/// Checked expansion of one postfix `?`. The checker builds and checks the
/// ordinary match/return tree once; typed-tree construction substitutes it for
/// the surface node so downstream phases need no propagation-specific form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropagationPlan {
    pub lowered: crate::node_kinds::expr::Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConformanceEvidence {
    pub row: ConformanceId,
    pub self_ty: Ty,
    pub protocol: ProtocolRef,
    pub witnesses: FxHashMap<String, Symbol>,
    pub substitution: Vec<(Symbol, Ty)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExistentialPack {
    pub existential: Ty,
    pub payload: Ty,
}

/// How a member access resolved. Concrete conformance dispatch publishes the
/// complete evidence lowering needs; generic and existential dispatch remains
/// an explicit protocol-requirement operation backed by a runtime dictionary.
#[derive(Clone, Debug, PartialEq, Eq)]
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

#[derive(Clone, Default, Debug)]
pub struct TypeOutput {
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
    pub member_resolutions: FxHashMap<NodeID, MemberResolution>,
    /// Exact rows selected while discharging call-site conformance
    /// obligations. Specialization carries these into generic bodies.
    pub conformance_evidence: FxHashMap<NodeID, Vec<ConformanceEvidence>>,
    /// Signed 64-bit values or explicit recovery for every integer literal
    /// expression and pattern (ledger row LIT-01).
    pub integer_literals: FxHashMap<NodeID, CheckedIntegerLiteral>,
    /// Per-`for`-statement iteration plans (keyed by the statement node).
    /// Consumed only by the typed-tree build, which elaborates the loop
    /// into ordinary nodes at the plan's ids.
    pub for_plans: FxHashMap<NodeID, ForPlan>,
    /// Checked match/return expansions for postfix early propagation.
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
