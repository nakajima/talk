#![feature(box_patterns)]
#![feature(stmt_expr_attributes)]
#![allow(clippy::uninlined_format_args)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]
#![cfg_attr(not(test), deny(clippy::expect_used))]
#![cfg_attr(not(test), deny(clippy::panic))]
#![cfg_attr(not(test), deny(clippy::todo))]
// #![cfg_attr(not(test), warn(clippy::unimplemented))]

pub mod parsing;
mod profile;
pub use parsing::*;
pub mod analysis;
pub mod common;
pub mod compiling;
pub use common::*;
pub mod desugar;
pub mod macro_expansion;
pub mod name_resolution;
pub mod procedural_macros;
pub mod repl;
pub mod testing;
pub mod typed_ast;
pub mod types;

#[cfg(feature = "cli")]
pub mod cli;

#[cfg(feature = "cli")]
pub mod lsp;

#[cfg(test)]
pub mod test_utils;

#[cfg(test)]
#[ctor::ctor]
pub fn init_tracing() {
    test_utils::trace::init()
}

// General helpers
#[macro_export]
macro_rules! map {
    ($value:expr, $func:expr) => {
        $value.iter().map($func).collect()
    };
}

#[macro_export]
macro_rules! map_into {
    ($value:expr, $func:expr) => {
        $value.into_iter().map($func).collect()
    };
}
