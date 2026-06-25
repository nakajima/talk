//! Type errors. Variants carry pre-rendered type strings so the error enum
//! stays `Hash + Eq` for `Diagnostic<E>` without dragging the solver's state
//! along (origins follow GHC's CtOrigin idea: every constraint knows the node
//! and reason it came from — OutsideIn(X) JFP 2011 reports residuals at their
//! generation site).

use std::error::Error;
use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeError {
    Mismatch {
        expected: String,
        found: String,
    },
    ArityMismatch {
        expected: usize,
        found: usize,
    },
    /// Occurs check failure — the infinite type of Robinson 1965's
    /// unification algorithm.
    InfiniteType {
        ty: String,
    },
    UnknownMember {
        receiver: String,
        label: String,
    },
    NotAFunction {
        found: String,
    },
    InvalidAssignmentTarget,
    AssignThroughSharedBorrow {
        target: String,
        ty: String,
    },
    NotConforming {
        ty: String,
        protocol: String,
    },
    /// Several protocols the receiver conforms to provide the member;
    /// committing to any would make the program's meaning depend on
    /// conformance-table order (the overlapping-instances coherence
    /// problem — Jones, *Qualified Types*, 1994, §2.4). The message names
    /// the protocol-static forms that pick one.
    AmbiguousMember {
        receiver: String,
        label: String,
        candidates: Vec<String>,
    },
    MissingWitness {
        protocol: String,
        requirement: String,
    },
    AmbiguousTypeParameter {
        param: String,
    },
    DuplicatePredicate {
        predicate: String,
    },
    InvalidWherePredicate,
    EscapingExistential {
        param: String,
    },
    GenericShadowing {
        name: String,
    },
    InvalidVariantResultType {
        variant: String,
    },
    RedundantVariantResultType {
        variant: String,
    },
    IncompatibleOrPatternRefinements,
    AmbiguousGadtMatchResult,
    InvalidExistentialProtocol {
        ty: String,
    },
    MissingAssociatedTypeBinding {
        protocol: String,
        assoc: String,
    },
    UnknownAssociatedTypeBinding {
        protocol: String,
        assoc: String,
    },
    DuplicateAssociatedTypeBinding {
        assoc: String,
    },
    NonObjectSafeExistential {
        protocol: String,
        reason: String,
    },
    UnsupportedExistentialUpcast {
        expected: String,
        found: String,
    },
    /// A closed effect annotation (`func f() 'a -> ()`) is an exact upper
    /// bound: performing anything outside it is an error. (Checked at the
    /// declaration, keeping arrow rows open — the deviation from Koka's
    /// open-coercions noted in generate/.)
    UndeclaredEffect {
        effect: String,
    },
    /// Some value of the scrutinee's type reaches no arm (the usefulness
    /// check of Maranget, *Warnings for pattern matching*, JFP 2007 —
    /// see src/types/exhaustiveness.rs). Carries example values rendered
    /// as patterns.
    NonExhaustiveMatch {
        missing: Vec<String>,
    },
    /// Everything this arm matches is already matched by an earlier arm
    /// (reported as a warning, not an error).
    UnreachableMatchArm,
    CannotInfer,
    Unsupported(String),
}

impl Error for TypeError {}

impl Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::Mismatch { expected, found } => {
                write!(f, "Type mismatch: expected {expected}, found {found}")
            }
            TypeError::ArityMismatch { expected, found } => {
                write!(
                    f,
                    "Wrong number of arguments: expected {expected}, found {found}"
                )
            }
            TypeError::InfiniteType { ty } => {
                write!(f, "Cannot construct infinite type: {ty}")
            }
            TypeError::UnknownMember { receiver, label } => {
                write!(f, "Unknown member '{label}' on {receiver}")
            }
            TypeError::NotAFunction { found } => {
                write!(f, "Cannot call non-function value of type {found}")
            }
            TypeError::InvalidAssignmentTarget => {
                write!(
                    f,
                    "Assignment target must be a variable or stored member path"
                )
            }
            TypeError::AssignThroughSharedBorrow { target, ty } => {
                write!(
                    f,
                    "Cannot assign through shared borrow '{target}' of type {ty}; use `mut func` for a mutable receiver"
                )
            }
            TypeError::NotConforming { ty, protocol } => {
                write!(f, "{ty} does not conform to {protocol}")
            }
            TypeError::AmbiguousMember {
                receiver,
                label,
                candidates,
            } => {
                let forms: Vec<String> = candidates
                    .iter()
                    .map(|p| format!("{p}.{label}(…)"))
                    .collect();
                write!(
                    f,
                    "Ambiguous member '{label}' on {receiver}: provided by {}. Name one explicitly: {}",
                    candidates.join(", "),
                    forms.join(" or ")
                )
            }
            TypeError::MissingWitness {
                protocol,
                requirement,
            } => {
                write!(f, "Missing '{requirement}' required by {protocol}")
            }
            TypeError::AmbiguousTypeParameter { param } => {
                write!(
                    f,
                    "Type parameter {param} is constrained but not determined by the declaration's type"
                )
            }
            TypeError::DuplicatePredicate { predicate } => {
                write!(f, "Duplicate where predicate: {predicate}")
            }
            TypeError::InvalidWherePredicate => {
                write!(
                    f,
                    "Where predicates must mention a declaration type parameter or Self"
                )
            }
            TypeError::EscapingExistential { param } => {
                write!(
                    f,
                    "Existential type {param} escapes this pattern arm; return or store it by packing into an expected protocol existential, or keep it inside the arm"
                )
            }
            TypeError::GenericShadowing { name } => {
                write!(
                    f,
                    "Generic parameter '{name}' shadows an enclosing generic parameter"
                )
            }
            TypeError::InvalidVariantResultType { variant } => {
                write!(
                    f,
                    "Variant result type for '{variant}' must be the enclosing enum with the correct number of type arguments"
                )
            }
            TypeError::RedundantVariantResultType { variant } => {
                write!(f, "Variant result type for '{variant}' is redundant")
            }
            TypeError::IncompatibleOrPatternRefinements => {
                write!(
                    f,
                    "Or-pattern alternatives introduce different GADT refinements; split them into separate arms"
                )
            }
            TypeError::AmbiguousGadtMatchResult => {
                write!(
                    f,
                    "Cannot infer this GADT match result; add a return or let annotation so constructor refinements have a rigid expected type"
                )
            }
            TypeError::InvalidExistentialProtocol { ty } => {
                write!(f, "'any' expects a protocol, found {ty}")
            }
            TypeError::MissingAssociatedTypeBinding { protocol, assoc } => {
                write!(
                    f,
                    "Missing associated type binding {assoc} for any {protocol}"
                )
            }
            TypeError::UnknownAssociatedTypeBinding { protocol, assoc } => {
                write!(
                    f,
                    "Unknown associated type binding {assoc} for any {protocol}"
                )
            }
            TypeError::DuplicateAssociatedTypeBinding { assoc } => {
                write!(
                    f,
                    "Duplicate associated type binding {assoc} in existential type"
                )
            }
            TypeError::NonObjectSafeExistential { protocol, reason } => {
                write!(f, "Cannot form any {protocol}: {reason}")
            }
            TypeError::UnsupportedExistentialUpcast { expected, found } => {
                write!(
                    f,
                    "Existential upcasting is not supported in v1: cannot use {found} as {expected}"
                )
            }
            TypeError::UndeclaredEffect { effect } => {
                write!(
                    f,
                    "Performs '{effect}, which the function's effect annotation does not declare"
                )
            }
            TypeError::NonExhaustiveMatch { missing } => {
                if missing.iter().all(|m| m == "_") {
                    write!(
                        f,
                        "Match does not cover every case; add a catch-all arm: _ -> …"
                    )
                } else {
                    write!(
                        f,
                        "Match does not cover every case; unhandled: {}",
                        missing.join(", ")
                    )
                }
            }
            TypeError::UnreachableMatchArm => {
                write!(
                    f,
                    "This arm never runs: the arms above it already match everything it could"
                )
            }
            TypeError::CannotInfer => {
                write!(f, "Cannot infer type; add an annotation")
            }
            TypeError::Unsupported(what) => {
                write!(f, "Not yet supported by the type checker: {what}")
            }
        }
    }
}
