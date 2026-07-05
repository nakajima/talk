//! The Talk type system: OutsideIn(X) (Vytiniotis, Peyton Jones, Schrijvers
//! & Sulzmann, JFP 2011) instantiated with equalities over types with record
//! rows (Leijen 2005) and effect rows (Koka, MSFP 2014), protocol conformance
//! predicates (Wadler & Blott 1989), and HasMember predicates (Gaster &
//! Jones 1996). Solving is scoped to one SCC binding group at a time; nothing
//! survives a group except finished schemes and output tables.

pub mod catalog;
pub mod constraint;
pub mod error;
pub mod exhaustiveness;
pub mod generate;
pub mod output;
pub mod solve;
pub mod ty;
pub mod variant;

#[cfg(test)]
pub mod types_tests;

pub use error::TypeError;
pub use output::TypeOutput;

/// Generalization depth for unification variables (OutsideIn's levels):
/// the checker works at `GROUP_LEVEL` inside a binding group and
/// `OUTER_LEVEL` outside; a variable generalizes when its level is
/// deeper than the point it escapes to.
#[derive(
    Default,
    PartialEq,
    PartialOrd,
    Ord,
    Clone,
    Copy,
    Debug,
    Eq,
    Hash,
    serde::Serialize,
    serde::Deserialize,
)]
pub struct Level(pub u32);

impl Level {
    pub fn next(&self) -> Level {
        Level(self.0 + 1)
    }

    pub fn prev(&self) -> Level {
        Level(self.0.saturating_sub(1))
    }
}
