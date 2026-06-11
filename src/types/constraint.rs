//! Constraints — the X in OutsideIn(X) (Vytiniotis, Peyton Jones, Schrijvers
//! & Sulzmann, JFP 2011) instantiated for Talk:
//!
//! - `Eq`: syntactic equality over `Ty`, including record rows (Leijen 2005)
//!   and effect rows (Koka, MSFP 2014) via decomposition in the solver.
//! - `Conforms(τ, P)`: protocol conformance — a class constraint in the sense
//!   of Wadler & Blott, POPL 1989 (solved from milestone 3).
//! - `HasMember`: a Has-style predicate (Gaster & Jones, TR NOTTCS-TR-96-3,
//!   1996) for member access on a type whose head is not yet known (solved
//!   from milestone 3).
//! - `Implic`: implication constraints carrying local given equalities under
//!   untouchability levels (OutsideIn(X) §5). v1 generates none; GADT match
//!   arms (milestone 8) will.
//!
//! Constraints are data with the lifetime of ONE binding group: created
//! during generation, consumed by one `solve` call, then dropped. No store
//! outlives a group — that discipline is the whole point.

use crate::label::Label;
use crate::name_resolution::scc_graph::Level;
use crate::node_id::NodeID;
use crate::types::ty::{EffectRow, Ty};

/// Why a constraint exists — the blame half of GHC's CtOrigin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CtReason {
    Annotation,
    Apply,
    Branch,
    Assignment,
    Return,
    Recursion,
    ArrayElement,
    Condition,
    Pattern,
    Body,
    Effect,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CtOrigin {
    pub node: NodeID,
    pub reason: CtReason,
}

impl CtOrigin {
    pub fn new(node: NodeID, reason: CtReason) -> Self {
        CtOrigin { node, reason }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    Eq(Ty, Ty, CtOrigin),
    EffEq(EffectRow, EffectRow, CtOrigin),
    /// `ty` conforms to `protocol`, with this use's expected associated-type
    /// bindings (fresh holes at a use site; concrete expectations when
    /// re-emitted from a scheme's bounds). Discharge equates each binding
    /// with the conformance's (Chakravarty et al., ICFP 2005).
    Conforms {
        ty: Ty,
        protocol: crate::name_resolution::symbol::Symbol,
        assoc: Vec<(crate::name_resolution::symbol::Symbol, Ty)>,
        origin: CtOrigin,
    },
    HasMember {
        receiver: Ty,
        label: Label,
        member: Ty,
        origin: CtOrigin,
    },
    Implic(Box<Implication>),
}

/// OutsideIn(X) §5: wanteds solved under local given equalities; variables
/// from outside `level` are untouchable inside.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Implication {
    pub level: Level,
    pub givens: Vec<Constraint>,
    pub wanteds: Vec<Constraint>,
}
