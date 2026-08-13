#![feature(stmt_expr_attributes)]
#![allow(clippy::uninlined_format_args)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]
#![cfg_attr(not(test), deny(clippy::expect_used))]
#![cfg_attr(not(test), deny(clippy::panic))]
#![cfg_attr(not(test), deny(clippy::todo))]
// #![cfg_attr(not(test), warn(clippy::unimplemented))]

// The frontend lives in its own crate (ADR 0057 slice 3b); re-exporting
// it whole keeps every historical `talk::…` and `crate::…` path working
// while Cargo enforces that frontend code cannot reach the toolchain.
pub use talk_front::*;
pub use talk_front::{
    common, desugar, front, macro_expansion, name_resolution, parsing, typed_ast, types,
};

mod profile;
pub mod analysis;
pub mod compiling;
pub mod procedural_macros;
pub mod repl;
pub mod testing;

#[cfg(feature = "cli")]
pub mod cli;

#[cfg(feature = "cli")]
pub mod lsp;

#[cfg(any(test, feature = "test-access"))]
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
