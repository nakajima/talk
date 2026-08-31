//! Phase-owned semantic program produced by frontend elaboration.
//!
//! Core is the interface between type checking and lowering. The parser tree
//! remains frontend input; downstream compiler phases receive an owned Core
//! value whose source identities and checked decisions are stable.

pub(crate) mod build;
pub mod facts;
mod nodes;
pub mod program;

pub use nodes::*;

use std::marker::PhantomData;

use indexmap::IndexMap;

use crate::front::source::Source;

mod phase {
    pub trait Sealed {}
}

/// A legal Core phase marker.
pub trait Phase: phase::Sealed + Clone + std::fmt::Debug + Send + Sync + 'static {
    type Repr: Clone;
}

/// Nested functions and source-shaped match control flow after elaboration.
#[derive(Clone, Copy, Debug, Default)]
pub struct Nested;

/// Pattern control flow has been flattened.
#[derive(Clone, Copy, Debug, Default)]
pub struct Flat;

/// Function environments have been closed explicitly.
#[derive(Clone, Copy, Debug, Default)]
pub struct Closed;

/// Every executable callable has a concrete specialization.
#[derive(Clone, Copy, Debug, Default)]
pub struct Mono;

impl phase::Sealed for Nested {}
impl phase::Sealed for Flat {}
impl phase::Sealed for Closed {}
impl phase::Sealed for Mono {}

impl Phase for Nested {
    type Repr = FileProgram;
}
impl Phase for Flat {
    type Repr = FileProgram;
}
impl Phase for Closed {
    type Repr = FileProgram;
}
impl Phase for Mono {
    type Repr = FileProgram;
}

/// Deterministically ordered semantic files.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct FileProgram {
    files: IndexMap<Source, TypedFile>,
}

/// A checked semantic program at phase `P`.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
#[serde(bound(
    serialize = "P::Repr: serde::Serialize",
    deserialize = "P::Repr: serde::Deserialize<'de>"
))]
pub struct Core<P: Phase> {
    repr: P::Repr,
    #[serde(skip)]
    phase: PhantomData<fn() -> P>,
}

impl Core<Nested> {
    pub(crate) fn new(files: IndexMap<Source, TypedFile>) -> Self {
        Self {
            repr: FileProgram { files },
            phase: PhantomData,
        }
    }
}

impl<P: Phase<Repr = FileProgram>> Core<P> {
    /// Semantic files in deterministic initialization order.
    pub fn files(&self) -> &IndexMap<Source, TypedFile> {
        &self.repr.files
    }

    /// Assert the construction invariants shared by tree-backed Core phases.
    pub fn assert_lint(&self) {
        for file in self.repr.files.values() {
            debug_assert!(
                file.roots.iter().all(|node| match node {
                    Node::Expr(expr) => !matches!(
                        expr.ty.as_ty(),
                        crate::types::ty::Ty::Eff(_) | crate::types::ty::Ty::Static(_)
                    ),
                    Node::Decl(_) | Node::Stmt(_) => true,
                }),
                "a non-value expression type reached Core"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_phase_markers_are_sealed_program_states() {
        fn phase<P: Phase>() {}
        phase::<Nested>();
        phase::<Flat>();
        phase::<Closed>();
        phase::<Mono>();
    }
}
