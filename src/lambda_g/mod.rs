//! λ_G — the graph-based λ-calculus IR of Leißa & Griebler, *SSA without
//! Dominance for Higher-Order Programs* (arXiv:2604.09961v2; full text in
//! `ssa-paper.md` at the repository root, which is the canonical reference
//! for this module). Functions float in a flat soup; φ-functions are
//! function variables; dominance is replaced by free-variable nesting
//! (paper Thm. 1: nesting implies dominance); inlining, specialization, and
//! loop peeling are all β-reduction (Table 2). Lineage: Thorin (CGO 2015),
//! MimIR (POPL 2025).

pub mod check;
pub mod eval;
pub mod expr;
pub mod fv;
pub mod nest;
pub mod print;
pub mod program;
pub mod sets;
pub mod subst;

#[cfg(test)]
pub mod lambda_g_tests;

pub use program::{Label, Program};
