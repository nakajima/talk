//! Callable argument-label contracts (ADR 0041).
//!
//! A named callable's source-level interface is its base name plus the
//! ordered external argument labels. The contract associates that key and
//! the declaration's role with an ordinary `Symbol`; symbols stay opaque
//! identities and lookup tables key overload sets by `CallableName`.

use std::fmt::Display;

use crate::node_kinds::parameter::Parameter;

/// One external argument-label slot of a callable (ADR 0041).
#[derive(
    Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum ArgumentLabel {
    /// The argument must be written `name: value`.
    Named(String),
    /// Declared `_` — the argument must be unlabeled.
    Omitted,
}

/// A source-level callable declaration key: the base name plus the ordered
/// external labels. Local binder names never participate (`func split(foo
/// fizz)` is `split(foo:)` regardless of `fizz`), and the implicit `self`
/// receiver is not part of the source-facing label list.
#[derive(
    Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct CallableName {
    pub base: String,
    pub labels: Vec<ArgumentLabel>,
}

impl CallableName {
    /// Build a callable name from declaration parameters, excluding the
    /// implicit receiver when the declaration carries one.
    pub fn from_params<'p>(
        base: impl Into<String>,
        params: impl IntoIterator<Item = &'p Parameter>,
        has_receiver: bool,
    ) -> Self {
        let labels = params
            .into_iter()
            .skip(usize::from(has_receiver))
            .map(|param| match param.external_label() {
                Some(name) => ArgumentLabel::Named(name),
                None => ArgumentLabel::Omitted,
            })
            .collect();
        Self {
            base: base.into(),
            labels,
        }
    }
}

impl Display for CallableName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}(", self.base)?;
        for label in &self.labels {
            match label {
                ArgumentLabel::Named(name) => write!(f, "{name}:")?,
                ArgumentLabel::Omitted => write!(f, "_:")?,
            }
        }
        write!(f, ")")
    }
}

/// One written argument slot at a call, for overload selection
/// (ADR 0041). Trailing blocks and paren-less leading strings omit their
/// labels by syntax and admit any declared label.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WrittenSlot {
    Named(String),
    Positional,
    Any,
}

impl WrittenSlot {
    pub fn of(arg: &crate::node_kinds::call_arg::CallArg) -> Self {
        use crate::node_kinds::call_arg::CallArgOrigin;
        match arg.origin {
            CallArgOrigin::TrailingBlock | CallArgOrigin::BareString => Self::Any,
            _ => match &arg.label {
                crate::label::Label::Named(label) => Self::Named(label.clone()),
                _ => Self::Positional,
            },
        }
    }
}

/// Whether a declared label sequence admits these written slots exactly.
pub fn labels_admit(declared: &[ArgumentLabel], written: &[WrittenSlot]) -> bool {
    declared.len() == written.len()
        && written
            .iter()
            .zip(declared)
            .all(|(slot, label)| match (slot, label) {
                (WrittenSlot::Any, _) => true,
                (WrittenSlot::Named(written), ArgumentLabel::Named(declared)) => {
                    written == declared
                }
                (WrittenSlot::Positional, ArgumentLabel::Omitted) => true,
                _ => false,
            })
}

/// The declaration kind a callable contract covers.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum CallableRole {
    /// A module or local named function.
    Function,
    /// An instance or static method (including witnesses, protocol
    /// defaults, and inherent extension members).
    Method { is_static: bool },
    /// An explicit or synthesized memberwise initializer.
    Init,
    /// A protocol method or initializer requirement.
    Requirement,
    /// An effect operation.
    Effect,
}

/// A named callable's argument-label contract, keyed by its declaration
/// `Symbol` in `TypeCatalog::callable_contracts`.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CallableContract {
    pub name: CallableName,
    pub role: CallableRole,
}
