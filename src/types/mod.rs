//! The Talk type system: OutsideIn(X) (Vytiniotis, Peyton Jones, Schrijvers
//! & Sulzmann, JFP 2011) instantiated with equalities over types with record
//! rows (Leijen 2005) and effect rows (Koka, MSFP 2014), protocol conformance
//! predicates (Wadler & Blott 1989), and HasMember predicates (Gaster &
//! Jones 1996). Solving is scoped to one SCC binding group at a time; nothing
//! survives a group except finished schemes and output tables.

pub mod catalog;
pub mod constraint;
pub mod error;
pub mod generate;
pub mod output;
pub mod solve;
pub mod ty;

#[cfg(test)]
pub mod types_tests;

pub use error::TypeError;
pub use output::TypeOutput;
