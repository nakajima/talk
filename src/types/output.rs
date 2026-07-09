//! The type checker's outputs: everything later phases consume. The lowerer
//! reads tables (schemes, per-call-site instantiations, member resolutions —
//! the dictionary-or-monomorphization surface of Wadler & Blott, POPL 1989);
//! it never asks the checker questions.

use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;
use crate::node_id::NodeID;
use crate::types::ty::{ProtocolRef, Scheme, Ty};

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
    /// Mut-mode (`for x in mut xs`) extras: the per-iteration
    /// `write_back(value)` call, its argument node (the binder read), and
    /// the loop-end `finish()` restore call. Unused for other modes.
    pub write_back_callee_id: NodeID,
    pub write_back_call_id: NodeID,
    pub write_back_arg_id: NodeID,
    pub finish_callee_id: NodeID,
    pub finish_call_id: NodeID,
    pub iterator_ty: Ty,
    pub element_ty: Ty,
    pub next_result_ty: Ty,
    /// The body block's value type: the per-iteration match join discards
    /// it, and the discard must drop droppable tails.
    pub body_ty: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExistentialPack {
    pub existential: Ty,
    pub payload: Ty,
}

/// How a member access resolved: directly on a nominal type, or through a
/// protocol requirement witnessed by a conformance (dictionary passing's
/// witness selection).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemberResolution {
    Direct(Symbol),
    ViaConformance {
        protocol: ProtocolRef,
        witness: Symbol,
    },
}

pub(crate) fn stored_field_symbol(
    types: &TypeOutput,
    resolution: Option<&MemberResolution>,
) -> Option<Symbol> {
    let MemberResolution::Direct(property) = resolution? else {
        return None;
    };
    let in_catalog = types.catalog.structs.values().any(|info| {
        info.fields
            .values()
            .any(|(field_symbol, _)| field_symbol == property)
    });
    let has_field_scheme = types
        .schemes
        .get(property)
        .is_some_and(|scheme| !matches!(scheme.ty, Ty::Func(..)));
    (in_catalog || has_field_scheme).then_some(*property)
}

#[derive(Clone, Default, Debug)]
pub struct TypeOutput {
    /// This module's slice of the type catalog (exported with the module).
    pub catalog: crate::types::catalog::TypeCatalog,
    /// Zonked type of every expression node — LSP hover and the lowerer.
    pub node_types: FxHashMap<NodeID, Ty>,
    /// Finished scheme for every top-level binder (monomorphic binders get
    /// empty-parameter schemes).
    pub schemes: FxHashMap<Symbol, Scheme>,
    /// Per use-site instantiation of a scheme's parameters: the
    /// "call sites and substitutions" surface the lowerer needs for
    /// monomorphization or dictionary passing.
    pub instantiations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    pub member_resolutions: FxHashMap<NodeID, MemberResolution>,
    /// Per-`for`-statement iteration plans (keyed by the statement node).
    /// Consumed only by the typed-tree build, which elaborates the loop
    /// into ordinary nodes at the plan's ids.
    pub for_plans: FxHashMap<NodeID, ForPlan>,
    /// Per-file low-water mark of the checker's descending id mint: the
    /// typed-tree build mints its elaborated-node ids below this.
    pub synthetic_floors: FxHashMap<crate::node_id::FileID, u32>,
    /// Argument nodes where a borrowed value satisfies an owned CheapClone
    /// parameter by cloning (an O(1) buffer retain, emitted by lowering).
    pub coerce_clones: rustc_hash::FxHashSet<NodeID>,
    /// Finalized types of monomorphic local binders (pattern binds
    /// included) — the flow checker's source for binder grades.
    pub local_tys: FxHashMap<Symbol, Ty>,
    /// Expression nodes implicitly packed into an existential expected type.
    /// Lowering turns these into payload-plus-witness-table packages.
    pub existential_packs: FxHashMap<NodeID, ExistentialPack>,
    /// Capability flow for the lowerer's abort analysis (lexical effect
    /// Imported + local symbol names, merged — what diagnostics rendered
    /// with during checking, so hover and the REPL show the same names.
    pub display_names: FxHashMap<Symbol, String>,
}
