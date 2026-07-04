//! Constraints — the X in OutsideIn(X) (Vytiniotis, Peyton Jones, Schrijvers
//! & Sulzmann, JFP 2011) instantiated for Talk:
//!
//! - `Eq`: syntactic equality over `Ty`, including record rows (Leijen,
//!   *Extensible Records with Scoped Labels*, TFP 2005) and effect rows
//!   (Leijen, *Koka: Programming with Row-Polymorphic Effect Types*,
//!   MSR-TR-2013-79) via decomposition in the solver.
//! - `Conforms(ty, P)`: protocol conformance — a class constraint in the
//!   sense of Wadler & Blott, POPL 1989.
//! - `HasMember`: a Has-style predicate (Gaster & Jones, TR NOTTCS-TR-96-3,
//!   1996) for member access on a type whose head is not yet known.
//! - `Implic`: implication constraints carrying local givens, optional
//!   untouchability levels, and GADT existentials (OutsideIn(X) §5).
//!   Declaration `where` clauses and GADT match arms both use givens; GADT
//!   arms additionally set touchability and local skolem parameters.
//!
//! Constraints are data with the lifetime of ONE binding group: created
//! during generation, consumed by one `solve` call, then dropped. No store
//! outlives a group — that discipline is the whole point.

use crate::label::Label;
use crate::name_resolution::scc_graph::Level;
use crate::node_id::NodeID;
use crate::types::ty::{EffectRow, Perm, Predicate, Ty};

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

impl CtReason {
    /// The reason for sub-constraints reached by structurally decomposing a
    /// constraint with this reason. Application-position auto-borrow coercion
    /// (`Apply`) is only valid at the immediate argument; once we descend under
    /// a type constructor the position may flip polarity (e.g. a function
    /// parameter is contravariant), so we drop `Apply` to force invariant
    /// unification. Other reasons are already non-coercing and pass through.
    pub fn nested(self) -> CtReason {
        match self {
            CtReason::Apply => CtReason::Body,
            other => other,
        }
    }
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

    /// The origin for sub-constraints reached by structurally decomposing this
    /// one. See [`CtReason::nested`]: application-position coercion does not
    /// survive descending under a type constructor.
    pub fn nested(self) -> CtOrigin {
        CtOrigin {
            reason: self.reason.nested(),
            ..self
        }
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
    /// Application-position auto-borrow whose argument type is not known yet.
    /// If `found` later resolves to a borrow, it is checked directly against
    /// the expected borrow; if it remains owned, it defaults to the usual
    /// owned-argument auto-borrow.
    ApplyBorrow {
        expected_perm: Perm,
        expected_inner: Ty,
        found: Ty,
        origin: CtOrigin,
    },
    /// The type a match's patterns check against: `scrutinee` with a
    /// top-level borrow stripped — patterns match through borrows
    /// (the runtime erases them; binders alias the borrowed payloads).
    /// Defers until the scrutinee's head resolves (e.g. an iterator
    /// element type solved by a conformance).
    PatternView {
        scrutinee: Ty,
        view: Ty,
        origin: CtOrigin,
    },
    /// A handler extent's row boundary (label-scoped elimination —
    /// docs/generic-effects-plan.md): every occurrence of `effects`'
    /// labels in `inner` is discharged by the covering `@handle`s; the
    /// remaining occurrences and `inner`'s residual tail flow to `outer`.
    /// Processed after the group's solve quiesces, when the extent's row
    /// content has surfaced.
    HandleEffect {
        inner: EffectRow,
        effects: Vec<crate::name_resolution::symbol::Symbol>,
        outer: EffectRow,
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
