#![feature(box_patterns)]
#![feature(stmt_expr_attributes)]
#![allow(clippy::uninlined_format_args)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]
#![cfg_attr(not(test), deny(clippy::expect_used))]
#![cfg_attr(not(test), deny(clippy::panic))]
#![cfg_attr(not(test), deny(clippy::todo))]

//! The Talk frontend: everything from source text to the elaborated
//! typed program (ADR 0057). Parsing vocabulary, hygiene, name
//! resolution, desugaring, macro expansion (through `front::macro_host`),
//! the type checker, and the typed tree. No toolchain, driver, or
//! backend code lives here — the `talk` crate implements the host seams
//! and re-exports these modules under their historical paths, so
//! `talk::types::…` and friends keep working.

pub mod parsing;
pub use parsing::*;

pub mod common;
pub use common::*;

pub mod desugar;
pub mod front;
pub mod macro_expansion;
pub mod name_resolution;
pub mod typed_ast;
pub mod types;
