//! Type errors. Variants carry pre-rendered type strings so the error enum
//! stays `Hash + Eq` for `Diagnostic<E>` without dragging the solver's state
//! along (origins follow GHC's CtOrigin idea: every constraint knows the node
//! and reason it came from — OutsideIn(X) JFP 2011 reports residuals at their
//! generation site).

use std::error::Error;
use std::fmt::Display;

use super::constraint::CtReason;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeError {
    Mismatch {
        expected: String,
        found: String,
        reason: CtReason,
    },
    ArityMismatch {
        expected: usize,
        found: usize,
    },
    IntegerLiteralOutOfRange {
        literal: String,
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
    UnknownMemberOnInferred {
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
    EqualityNotSupported {
        lhs: String,
        rhs: String,
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
    OverlappingConformance {
        ty: String,
        protocol: String,
        existing: String,
    },
    /// The `where` equalities over instance-head parameters have no common
    /// solution (ADR 0036 head refinement).
    ContradictoryHeadRefinement {
        first: String,
        second: String,
    },
    AmbiguousTypeParameter {
        param: String,
    },
    DuplicatePredicate {
        predicate: String,
    },
    InvalidWherePredicate,
    /// A static value expression (ADR 0035) appeared where a type is
    /// required. Static expressions are only meaningful as generic
    /// arguments to a declared `static` parameter.
    StaticValueInTypePosition,
    /// A `static` generic parameter declared a value type outside the
    /// admitted static domain (ADR 0035): `Int`, `Bool`, or a fieldless
    /// enum.
    UnsupportedStaticParamType {
        ty: String,
    },
    /// A generic argument to a `static` parameter was an ordinary type
    /// (or an unsupported expression form) rather than a static value.
    ExpectedStaticArgument {
        found: String,
    },
    /// The static index language is affine (ADR 0035): multiplication
    /// needs a literal operand.
    NonlinearStaticExpression,
    /// A static ordering obligation the checker could not prove within
    /// the supported linear-integer theory (ADR 0035 §4). The checker
    /// never assumes a predicate.
    UnprovenStaticPredicate {
        predicate: String,
    },
    /// A generic-parameter default that breaks the declaration rules
    /// (ADR 0035 §1): forward reference or negative static Int value.
    InvalidGenericDefault {
        reason: String,
    },
    /// A static argument the solve left without a unique solution
    /// (ADR 0035 §5): inference solves only uniquely-determined static
    /// equalities, so this use needs explicit generic arguments.
    UnderdeterminedStaticArgument,
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
    InvalidVariantPayloadLabels {
        variant: String,
    },
    DuplicateVariantPayloadLabel {
        variant: String,
        label: String,
    },
    IncompatibleOrPatternRefinements,
    AmbiguousGadtMatchResult,
    /// A user-written `mut`/`consume` parameter mode on an annotation that
    /// already spells a borrow (ADR 0018): the mode and the `&` are rival
    /// spellings of the same decision, so dropping either is a fix.
    ParamModeBorrowConflict {
        mode: String,
        annotation: String,
    },
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
    /// A user-declared effect flowed into a closed ambient row: nothing
    /// between the perform and the top level installs a handler for it
    /// (the runtime implicitly handles only the core effects).
    UnhandledEffect {
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
    UnreachableCode,
    CannotInfer,
    /// A `Copy`/`CheapClone` conformance whose fields don't support it.
    NonConformingField {
        protocol: String,
        field: String,
        ty: String,
    },
    /// A method used as a value (`x.method` with no call): no lowering
    /// exists for bound-method values yet, so typing owns the rejection —
    /// this must never surface as a lowerer error.
    MethodReference {
        label: String,
    },
    /// A `linear` declaration claiming a conformance that would defeat
    /// linearity (`Copy` duplicates it, `Deinit` silently discards it).
    LinearConformance {
        ty: String,
        protocol: String,
    },
    HeapConformance {
        ty: String,
        protocol: String,
    },
    /// A `Deinit` hook whose row carries a user effect: drop glue calls
    /// deinit through a fixed signature with no capability parameters, so
    /// the handler could never reach the body (ADR 0027).
    DeinitEffectRow {
        ty: String,
        effect: String,
    },
    /// A leading-dot variant use whose enum was never determined by
    /// context — nothing to resolve `.label` against.
    UnresolvedVariant {
        label: String,
    },
    InvalidEarlyPropagation {
        reason: String,
    },
    RecursiveConformance {
        constraint: String,
    },
    /// The solver hit its hard work limit. This is a fail-closed guard: a
    /// recursive conformance or associated-type cycle must become a diagnostic,
    /// never an unbounded compiler or LSP hang.
    SolverOverflow {
        limit: usize,
        constraint: String,
    },
    Unsupported(String),
}

impl Error for TypeError {}

impl TypeError {
    pub fn code(&self) -> &'static str {
        match self {
            Self::Mismatch { .. } => "type.mismatch",
            Self::ArityMismatch { .. } => "type.arity-mismatch",
            Self::IntegerLiteralOutOfRange { .. } => "type.integer-literal-out-of-range",
            Self::InfiniteType { .. } => "type.infinite-type",
            Self::UnknownMember { .. } => "type.unknown-member",
            Self::UnknownMemberOnInferred { .. } => "type.unknown-member-on-inferred",
            Self::NotAFunction { .. } => "type.not-a-function",
            Self::InvalidAssignmentTarget => "type.invalid-assignment-target",
            Self::AssignThroughSharedBorrow { .. } => "type.assign-through-shared-borrow",
            Self::NotConforming { .. } => "type.not-conforming",
            Self::EqualityNotSupported { .. } => "type.equality-not-supported",
            Self::AmbiguousMember { .. } => "type.ambiguous-member",
            Self::MissingWitness { .. } => "type.missing-witness",
            Self::OverlappingConformance { .. } => "type.overlapping-conformance",
            Self::ContradictoryHeadRefinement { .. } => "type.contradictory-head-refinement",
            Self::AmbiguousTypeParameter { .. } => "type.ambiguous-type-parameter",
            Self::DuplicatePredicate { .. } => "type.duplicate-predicate",
            Self::InvalidWherePredicate => "type.invalid-where-predicate",
            Self::StaticValueInTypePosition => "type.static-value-in-type-position",
            Self::UnsupportedStaticParamType { .. } => "type.unsupported-static-param-type",
            Self::ExpectedStaticArgument { .. } => "type.expected-static-argument",
            Self::NonlinearStaticExpression => "type.nonlinear-static-expression",
            Self::UnprovenStaticPredicate { .. } => "type.unproven-static-predicate",
            Self::InvalidGenericDefault { .. } => "type.invalid-generic-default",
            Self::UnderdeterminedStaticArgument => "type.underdetermined-static-argument",
            Self::EscapingExistential { .. } => "type.escaping-existential",
            Self::GenericShadowing { .. } => "type.generic-shadowing",
            Self::InvalidVariantResultType { .. } => "type.invalid-variant-result-type",
            Self::RedundantVariantResultType { .. } => "type.redundant-variant-result-type",
            Self::InvalidVariantPayloadLabels { .. } => "type.invalid-variant-payload-labels",
            Self::DuplicateVariantPayloadLabel { .. } => "type.duplicate-variant-payload-label",
            Self::IncompatibleOrPatternRefinements => "type.incompatible-or-pattern-refinements",
            Self::AmbiguousGadtMatchResult => "type.ambiguous-gadt-match-result",
            Self::ParamModeBorrowConflict { .. } => "type.param-mode-borrow-conflict",
            Self::InvalidExistentialProtocol { .. } => "type.invalid-existential-protocol",
            Self::MissingAssociatedTypeBinding { .. } => "type.missing-associated-type-binding",
            Self::UnknownAssociatedTypeBinding { .. } => "type.unknown-associated-type-binding",
            Self::DuplicateAssociatedTypeBinding { .. } => "type.duplicate-associated-type-binding",
            Self::NonObjectSafeExistential { .. } => "type.non-object-safe-existential",
            Self::UnsupportedExistentialUpcast { .. } => "type.unsupported-existential-upcast",
            Self::UndeclaredEffect { .. } => "type.undeclared-effect",
            Self::UnhandledEffect { .. } => "type.unhandled-effect",
            Self::NonExhaustiveMatch { .. } => "type.non-exhaustive-match",
            Self::UnreachableMatchArm => "type.unreachable-match-arm",
            Self::UnreachableCode => "type.unreachable-code",
            Self::CannotInfer => "type.cannot-infer",
            Self::NonConformingField { .. } => "type.non-conforming-field",
            Self::MethodReference { .. } => "type.method-reference",
            Self::LinearConformance { .. } => "type.linear-conformance",
            Self::HeapConformance { .. } => "type.heap-conformance",
            Self::DeinitEffectRow { .. } => "type.deinit-effect-row",
            Self::UnresolvedVariant { .. } => "type.unresolved-variant",
            Self::InvalidEarlyPropagation { .. } => "type.invalid-early-propagation",
            Self::RecursiveConformance { .. } => "type.recursive-conformance",
            Self::SolverOverflow { .. } => "type.solver-overflow",
            Self::Unsupported(_) => "type.unsupported",
        }
    }
}

impl Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::Mismatch {
                expected,
                found,
                reason,
            } => match reason {
                CtReason::Annotation => write!(
                    f,
                    "Type mismatch in annotated expression: the annotation requires {expected}, but the expression has type {found}"
                ),
                CtReason::Apply | CtReason::NestedApply => write!(
                    f,
                    "Type mismatch in function argument: the parameter requires {expected}, but the argument has type {found}"
                ),
                CtReason::EqualityComparison => write!(
                    f,
                    "Cannot compare values of type {expected} and {found} for equality"
                ),
                CtReason::Branch | CtReason::GadtBranch => write!(
                    f,
                    "Type mismatch between branches: one branch has type {expected}, but another has type {found}; all branches must have the same type"
                ),
                CtReason::Assignment => write!(
                    f,
                    "Type mismatch in assignment: the target requires {expected}, but the assigned value has type {found}"
                ),
                CtReason::Return => write!(
                    f,
                    "Type mismatch in return value: the function requires {expected}, but the returned expression has type {found}"
                ),
                CtReason::Recursion => write!(
                    f,
                    "Type mismatch in recursive definition: earlier uses require {expected}, but the definition has type {found}"
                ),
                CtReason::ArrayElement => write!(
                    f,
                    "Type mismatch in array element: the array requires elements of type {expected}, but this element has type {found}"
                ),
                CtReason::InlineArrayLength => write!(
                    f,
                    "InlineArray literal has {found} elements, but its type requires {expected}"
                ),
                CtReason::Condition => write!(
                    f,
                    "Type mismatch in condition: a condition must have type {expected}, but this expression has type {found}"
                ),
                CtReason::Pattern => write!(
                    f,
                    "Type mismatch in pattern: the matched value has type {expected}, but this pattern requires {found}"
                ),
                CtReason::Effect => write!(
                    f,
                    "Type mismatch in effects: the surrounding context allows {expected}, but this expression has {found}"
                ),
                CtReason::Body => write!(
                    f,
                    "Type mismatch in expression: the surrounding context requires {expected}, but this expression has type {found}"
                ),
            },
            TypeError::ArityMismatch { expected, found } => {
                write!(
                    f,
                    "Wrong number of arguments: expected {expected}, found {found}"
                )
            }
            TypeError::IntegerLiteralOutOfRange { literal } => write!(
                f,
                "Integer literal {literal} is outside the signed 64-bit range"
            ),
            TypeError::InfiniteType { ty } => {
                write!(f, "Cannot construct infinite type: {ty}")
            }
            TypeError::UnknownMember { receiver, label } => {
                write!(f, "Unknown member '{label}' on {receiver}")
            }
            TypeError::UnknownMemberOnInferred { label } => {
                write!(
                    f,
                    "Unknown member '{label}' on the inferred result of this expression"
                )
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
            TypeError::EqualityNotSupported { lhs, rhs } => {
                write!(f, "Cannot compare {lhs} with {rhs} for equality")
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
            TypeError::OverlappingConformance {
                ty,
                protocol,
                existing,
            } => {
                write!(
                    f,
                    "Overlapping conformance for {ty}: {protocol} overlaps existing {existing}"
                )
            }
            TypeError::ContradictoryHeadRefinement { first, second } => {
                write!(
                    f,
                    "Contradictory head refinement: {first} and {second} cannot be equal"
                )
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
            TypeError::StaticValueInTypePosition => {
                write!(
                    f,
                    "A static value expression is not a type; it can only be a generic argument to a `static` parameter"
                )
            }
            TypeError::UnsupportedStaticParamType { ty } => {
                write!(
                    f,
                    "A static parameter's value type must be Int, Bool, or a fieldless enum; got {ty}"
                )
            }
            TypeError::ExpectedStaticArgument { found } => {
                write!(
                    f,
                    "This generic argument supplies a static parameter, so it must be a static value expression; got {found}"
                )
            }
            TypeError::NonlinearStaticExpression => {
                write!(
                    f,
                    "Static multiplication needs an integer literal operand; the product of two symbolic values is outside the affine index language"
                )
            }
            TypeError::UnprovenStaticPredicate { predicate } => {
                write!(
                    f,
                    "Cannot prove the static predicate {predicate}; add it to (or strengthen) the declaration's where clause"
                )
            }
            TypeError::InvalidGenericDefault { reason } => {
                write!(f, "Invalid generic parameter default: {reason}")
            }
            TypeError::UnderdeterminedStaticArgument => {
                write!(
                    f,
                    "Cannot infer this static argument; supply explicit generic arguments"
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
            TypeError::InvalidVariantPayloadLabels { variant } => {
                write!(
                    f,
                    "Payload labels for variant '{variant}' must match its declaration order"
                )
            }
            TypeError::DuplicateVariantPayloadLabel { variant, label } => {
                write!(
                    f,
                    "Variant '{variant}' declares payload label '{label}' more than once"
                )
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
            TypeError::ParamModeBorrowConflict { mode, annotation } => {
                write!(
                    f,
                    "Parameter mode `{mode}` conflicts with its type: {annotation} is already a borrow. The mode decides borrowing — drop the `&` from the annotation, or drop the mode"
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
            TypeError::UnhandledEffect { effect } => {
                write!(
                    f,
                    "No handler for '{effect}: the effect reaches the top level unhandled"
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
            TypeError::UnreachableCode => {
                write!(f, "This code is unreachable")
            }
            TypeError::CannotInfer => {
                write!(f, "Cannot infer type; add an annotation")
            }
            TypeError::NonConformingField {
                protocol,
                field,
                ty,
            } => {
                write!(
                    f,
                    "Cannot conform to {protocol}: field `{field}` has type {ty}, which is not {protocol}"
                )
            }
            TypeError::MethodReference { label } => {
                write!(
                    f,
                    "Cannot use method '{label}' as a value yet: call it, or wrap it in a closure"
                )
            }
            TypeError::LinearConformance { ty, protocol } => {
                write!(
                    f,
                    "`{ty}` is linear and cannot conform to {protocol}: a linear value must be consumed exactly once"
                )
            }
            TypeError::HeapConformance { ty, protocol } => {
                write!(
                    f,
                    "`{ty}` is 'heap and cannot conform to {protocol}: heap values are shared by reference"
                )
            }
            TypeError::DeinitEffectRow { ty, effect } => {
                write!(
                    f,
                    "`{ty}`'s Deinit hook performs '{effect}: deinit runs from drop glue, which passes no effect capabilities — handle the effect inside the body"
                )
            }
            TypeError::UnresolvedVariant { label } => {
                write!(
                    f,
                    "Cannot infer the enum for '.{label}'; add a type annotation"
                )
            }
            TypeError::InvalidEarlyPropagation { reason } => {
                write!(f, "Cannot use '?' here: {reason}")
            }
            TypeError::RecursiveConformance { constraint } => {
                write!(
                    f,
                    "Recursive protocol conformance while checking `{constraint}`"
                )
            }
            TypeError::SolverOverflow { limit, constraint } => {
                write!(
                    f,
                    "Recursive protocol conformance while checking `{constraint}`. The type checker stopped at its safety limit ({limit} steps) instead of hanging. This usually means an associated type or default protocol method depends on the conformance currently being checked; add an explicit associated type binding or rewrite the default to break the cycle."
                )
            }
            TypeError::Unsupported(what) => {
                write!(f, "Not yet supported by the type checker: {what}")
            }
        }
    }
}
