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
    NotConforming {
        ty: String,
        protocol: String,
    },
    /// The unique-owner improvement rule found multiple candidate owners —
    /// never guess; ask for an annotation (Jones FPCA 1995 improvement must
    /// be justified by uniqueness).
    AmbiguousMember {
        label: String,
        candidates: Vec<String>,
    },
    MissingWitness {
        protocol: String,
        requirement: String,
    },
    /// A closed effect annotation (`func f() 'a -> ()`) is an exact upper
    /// bound: performing anything outside it is an error. (Checked at the
    /// declaration, keeping arrow rows open — the deviation from Koka's
    /// open-coercions noted in generate.rs.)
    UndeclaredEffect {
        effect: String,
    },
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
            TypeError::NotConforming { ty, protocol } => {
                write!(f, "{ty} does not conform to {protocol}")
            }
            TypeError::AmbiguousMember { label, candidates } => {
                write!(
                    f,
                    "Cannot infer the type providing '{label}'; candidates: {}. Add an annotation",
                    candidates.join(", ")
                )
            }
            TypeError::MissingWitness {
                protocol,
                requirement,
            } => {
                write!(f, "Missing '{requirement}' required by {protocol}")
            }
            TypeError::UndeclaredEffect { effect } => {
                write!(
                    f,
                    "Performs '{effect}, which the function's effect annotation does not declare"
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
