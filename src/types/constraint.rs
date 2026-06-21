//! Constraints — the X in OutsideIn(X) (Vytiniotis, Peyton Jones, Schrijvers
//! & Sulzmann, JFP 2011) instantiated for Talk:
//!
//! - `Eq`: syntactic equality over `Ty`, including record rows (Leijen,
//!   *Extensible Records with Scoped Labels*, TFP 2005) and effect rows
//!   (Leijen, *Koka: Programming with Row-Polymorphic Effect Types*,
//!   MSR-TR-2013-79) via decomposition in the solver.
//! - `Conforms(ty, P)`: protocol conformance — a class constraint in the
//!   sense of Wadler & Blott, POPL 1989 (solved from milestone 3).
//! - `HasMember`: a Has-style predicate (Gaster & Jones, TR NOTTCS-TR-96-3,
//!   1996) for member access on a type whose head is not yet known (solved
//!   from milestone 3).
//! - `Implic`: implication constraints carrying local givens, optional
//!   untouchability levels, and future GADT existentials (OutsideIn(X) §5).
//!   Declaration `where` clauses already use givens; GADT match arms will
//!   additionally set touchability and local skolem parameters.
//!
//! Constraints are data with the lifetime of ONE binding group: created
//! during generation, consumed by one `solve` call, then dropped. No store
//! outlives a group — that discipline is the whole point.

use crate::label::Label;
use crate::name_resolution::scc_graph::Level;
use crate::node_id::NodeID;
use crate::types::ty::{EffectRow, Predicate, Ty};

/// Why a constraint exists — the blame half of GHC's CtOrigin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CtReason {
    Annotation,
    Apply,
    Branch,
    GadtBranch,
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

impl Predicate {
    pub(crate) fn into_constraint(self, origin: CtOrigin) -> Constraint {
        match self {
            Predicate::TypeEq(a, b) => Constraint::Eq(a, b, origin),
            Predicate::EffectEq(a, b) => Constraint::EffEq(a, b, origin),
            Predicate::RowEq(a, b) => Constraint::Eq(Ty::Record(a), Ty::Record(b), origin),
            Predicate::Conforms { ty, protocol } => Constraint::Conforms {
                ty,
                protocol,
                origin,
            },
            Predicate::HasMember {
                receiver,
                label,
                member,
            } => Constraint::HasMember {
                receiver,
                label,
                member,
                origin,
            },
        }
    }
}

/// OutsideIn(X) implication constraints (Vytiniotis, Peyton Jones,
/// Schrijvers, Sulzmann, JFP 2011): wanteds solved under local givens. When
/// `touchable_level` is set, variables from outside that level are
/// untouchable inside. `local_params` are rigid skolems introduced by GADT
/// patterns; Peyton Jones, Vytiniotis, Weirich, and Washburn (ICFP 2006)
/// describe such constructor-local variables as existential and non-escaping.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Implication {
    pub level: Level,
    pub givens: Vec<Predicate>,
    pub wanteds: Vec<Constraint>,
    pub local_params: Vec<crate::name_resolution::symbol::Symbol>,
    pub touchable_level: Option<Level>,
}
