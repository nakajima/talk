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
use crate::node_id::NodeID;
use crate::types::Level;
use crate::types::ty::{EffectRow, Perm, Predicate, Ty};

/// Why a constraint exists — the blame half of GHC's CtOrigin.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CtReason {
    Annotation,
    Apply,
    /// The conformance selected by a surface `==` or `!=` expression.
    EqualityComparison,
    /// A constraint originating in an argument, after structural
    /// decomposition has crossed the application boundary. It retains the
    /// argument context for diagnostics without enabling application-only
    /// coercions in the solver.
    NestedApply,
    /// A mismatch in the parameter type of a function value supplied as an
    /// argument, such as a callback or trailing block.
    CallbackParameter,
    /// A mismatch in the result type of a function value supplied as an
    /// argument, such as a callback or trailing block.
    CallbackResult,
    Branch,
    GadtBranch,
    Assignment,
    Return,
    Recursion,
    ArrayElement,
    /// Equality between an InlineArray literal's element count and the
    /// exact count required by its contextual type.
    InlineArrayLength,
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
            CtReason::Apply => CtReason::NestedApply,
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
    /// One effect row must flow into another. Calls use this as the
    /// application subeffecting rule; explicit function annotations use it
    /// to publish the declared row while retaining a structured diagnostic
    /// for each inferred label outside that bound.
    EffectSubset {
        inferred: EffectRow,
        allowed: EffectRow,
        origin: CtOrigin,
    },
    /// `ty` conforms to `protocol`, with this use's expected associated-type
    /// bindings (fresh holes at a use site; concrete expectations when
    /// re-emitted from a scheme's bounds). Discharge equates each binding
    /// with the conformance's (Chakravarty et al., ICFP 2005).
    Conforms {
        ty: Ty,
        protocol: crate::types::ty::ProtocolRef,
        origin: CtOrigin,
    },
    /// A ranked same-type preference for an otherwise heterogeneous
    /// operation. Hard constraints solve first; at quiescence, if either side
    /// is still an unbound variable, the solver equates them and retries. If
    /// both sides independently resolved, the preference is discarded. This
    /// models the preferred same-type equality overload without preventing an
    /// `Equatable<RHS>` conformance from supporting a concrete cross-type use.
    PreferEq(Ty, Ty, CtOrigin),
    HasMember {
        receiver: Ty,
        label: Label,
        member: Ty,
        origin: CtOrigin,
    },
    /// A leading-dot variant use (`.some(1)`) in inference position: the
    /// enum arrives through unification rather than the checking mode, so
    /// resolution defers until `enum_ty`'s head is known — the same
    /// discipline as `HasMember`. `payload` carries each written argument's
    /// label and inferred type until the enum metadata is available. `ctor`
    /// is the callee node's type variable when the dot is a call's callee,
    /// unified with the constructor's function type on discharge.
    HasVariant {
        enum_ty: Ty,
        label: Label,
        payload: Vec<(Label, Ty)>,
        ctor: Option<Ty>,
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
    /// Application-position owned-`Param` slot whose argument type is not
    /// known yet (a call result still being solved). If `found` later
    /// resolves to a borrow, the argument satisfies the owned slot by a
    /// clone recorded at the origin node — elided or emitted per
    /// instantiation by lowering (ADR 0021). Otherwise it is the plain
    /// equality this deferral replaced.
    CoerceOwned {
        expected: Ty,
        found: Ty,
        origin: CtOrigin,
    },
    /// The type one pattern occurrence checks against, with a borrow at that
    /// occurrence stripped. Aggregate children create their own views, so a
    /// tuple can contain borrowed enum occurrences without changing the
    /// tuple's type. Defers until the occurrence head resolves.
    PatternView {
        scrutinee: Ty,
        view: Ty,
        origin: CtOrigin,
    },
    /// A string literal pattern accepts exactly String and Substring. This
    /// defers while a call result's nominal head is unresolved.
    StringPattern {
        ty: Ty,
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
    /// A static integer relation wanted (ADR 0035). Equality delegates
    /// to unification over the affine forms; orderings solve by
    /// evaluation when closed, entailment from givens when rigid, and
    /// defer while metavariables remain.
    StaticCmp {
        op: crate::types::ty::StaticCmpOp,
        lhs: Ty,
        rhs: Ty,
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
            Predicate::StaticCmp { op, lhs, rhs } => Constraint::StaticCmp {
                op,
                lhs,
                rhs,
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
