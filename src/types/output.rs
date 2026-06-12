//! The type checker's outputs: everything later phases consume. The future
//! lowerer reads tables (schemes, per-call-site instantiations, member
//! resolutions — the dictionary-or-monomorphization surface of Wadler &
//! Blott, POPL 1989); it never asks the checker questions.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::name_resolution::symbol::Symbol;
use crate::node_id::NodeID;
use crate::types::ty::{Scheme, Ty};

/// How a member access resolved: directly on a nominal type, or through a
/// protocol requirement witnessed by a conformance (dictionary passing's
/// witness selection).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemberResolution {
    Direct(Symbol),
    ViaConformance { protocol: Symbol, witness: Symbol },
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
    /// Capability flow for the lowerer's abort analysis (lexical effect
    /// handlers compile capability-passing — Brachthäuser, Schuster &
    /// Ostermann, "Effects as Capabilities", OOPSLA 2020; Schuster et
    /// al., PLDI 2022): which lexical handlers each binder's body
    /// performs into, recorded as the checker discharges the routed
    /// perform from the row.
    pub performs_into: FxHashMap<Symbol, FxHashSet<Symbol>>,
    /// Named symbols each binder's body references — a conservative
    /// superset of its calls, the edges for the abort analysis's
    /// transitive closure. A spurious edge only costs a callee the
    /// abort-capable calling convention, never correctness.
    pub binder_refs: FxHashMap<Symbol, FxHashSet<Symbol>>,
    /// Each `@handle`'s payload types, zonked (unannotated effect
    /// parameters are inferred from the perform sites that unified with
    /// them): handler symbol → parameter types.
    pub handler_payload_tys: FxHashMap<Symbol, Vec<Ty>>,
}
