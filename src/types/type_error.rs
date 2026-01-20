use std::{error::Error, fmt::Display};

use crate::{
    name::Name,
    name_resolution::symbol::{ProtocolId, Symbol},
    types::{
        conformance::ConformanceKey, constraints::constraint::ConstraintCause, infer_ty::InferTy,
        matcher::RequiredConstructor,
    },
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeError {
    TypeConstructorNotFound(Symbol),
    ExpectedRow(InferTy),
    GenericArgCount {
        expected: u8,
        actual: u8,
    },
    AmbiguousWitness {
        conformance_key: ConformanceKey,
        label: String,
    },
    InvalidUnification(Box<InferTy>, Box<InferTy>, Option<ConstraintCause>),
    OccursCheck(InferTy),
    CalleeNotCallable(InferTy),
    MemberNotFound(InferTy, String),
    NameNotResolved(Name),
    MissingConformanceRequirement(String),
    TypeNotFound(String),
    TypeDoesNotConform {
        symbol: Symbol,
        protocol_id: ProtocolId,
    },
    TypeCannotConform {
        ty: InferTy,
        protocol_id: ProtocolId,
    },
    NonExhaustiveMatch(Vec<RequiredConstructor>),
    UselessMatchArm,
    OrPatternBinderMismatch,
    RecordPatternMissingFields(Vec<String>),
    RecordPatternNeedsRest,
    EffectNotFound(String),
    UnhandledEffect(String),
    HandlerMustBeBound,
    ContinueOutsideHandler,
    SpecializationMismatch,
}

impl Error for TypeError {}
impl Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AmbiguousWitness {
                conformance_key,
                label,
            } => write!(f, "Ambiguous witness for {conformance_key:?}.{label}"),
            Self::TypeConstructorNotFound(id) => write!(f, "Type constructor not found: {id:?}"),
            Self::GenericArgCount { expected, actual } => {
                write!(f, "Expected {expected} type arguments, got {actual}")
            }
            Self::InvalidUnification(lhs, rhs, cause) => {
                if let Some(cause) = cause {
                    write!(
                        f,
                        "Type mismatch in {}: {} vs {}",
                        cause.label(),
                        lhs.as_ref(),
                        rhs.as_ref()
                    )
                } else {
                    write!(f, "Type mismatch: {} vs {}", lhs.as_ref(), rhs.as_ref())
                }
            }
            Self::OccursCheck(ty) => {
                write!(f, "Recursive type not supported..... yet? {ty:?}")
            }
            Self::ExpectedRow(ty) => {
                write!(f, "Expected row, got {ty:?}")
            }
            Self::MemberNotFound(ty, name) => {
                write!(f, "{ty:?} has no member: {name}")
            }
            Self::CalleeNotCallable(ty) => write!(f, "Callee not callable: {ty:?}"),
            Self::TypeNotFound(string) => write!(f, "{string}"),
            Self::MissingConformanceRequirement(string) => {
                write!(f, "Missing conformance requirement: {string:?}")
            }
            Self::TypeDoesNotConform { .. } => {
                write!(f, "Type does not conform wip")
            }
            Self::TypeCannotConform { ty, .. } => {
                write!(f, "Type cannot conform: {ty:?}")
            }
            Self::NameNotResolved(name) => {
                write!(f, "Name not resolved: {name:?}")
            }
            Self::NonExhaustiveMatch(cases) => {
                write!(f, "Match not exhaustive: {cases:?}")
            }
            Self::UselessMatchArm => {
                write!(f, "Useless match arm")
            }
            Self::OrPatternBinderMismatch => {
                write!(
                    f,
                    "Or-patterns must bind the same names in each alternative"
                )
            }
            Self::RecordPatternMissingFields(fields) => {
                write!(f, "Record pattern missing fields: {fields:?}")
            }
            Self::RecordPatternNeedsRest => {
                write!(f, "Record pattern on an open row must include `..`")
            }
            Self::EffectNotFound(name) => {
                write!(f, "Effect not found: {name}")
            }
            Self::UnhandledEffect(name) => {
                write!(
                    f,
                    "Effect '{name}' is not handled. Add a handler or declare the effect in the function signature."
                )
            }
            Self::HandlerMustBeBound => {
                write!(f, "Effect handlers must be bound to a name")
            }
            Self::ContinueOutsideHandler => {
                write!(f, "continue with a value is only valid inside a handler")
            }
            Self::SpecializationMismatch => {
                write!(f, "cannot determine specializations")
            }
        }
    }
}

impl TypeError {
    pub fn invalid_unification(lhs: InferTy, rhs: InferTy) -> Self {
        Self::InvalidUnification(lhs.into(), rhs.into(), None)
    }

    pub fn with_cause(self, cause: ConstraintCause) -> Self {
        match self {
            Self::InvalidUnification(lhs, rhs, None) => {
                Self::InvalidUnification(lhs, rhs, Some(cause))
            }
            Self::InvalidUnification(lhs, rhs, Some(existing)) => {
                Self::InvalidUnification(lhs, rhs, Some(existing))
            }
            other => other,
        }
    }

    pub fn with_optional_cause(self, cause: Option<ConstraintCause>) -> Self {
        match cause {
            Some(cause) => self.with_cause(cause),
            None => self,
        }
    }
}
