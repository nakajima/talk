#![feature(box_patterns)]
#![feature(associated_type_defaults)]
#![feature(assert_matches)]
#![feature(iter_advance_by)]
#![feature(if_let_guard)]
#![feature(hash_set_entry)]
#![feature(stmt_expr_attributes)]
#![feature(error_generic_member_access)]
#![feature(try_blocks)]
#![feature(try_trait_v2)]
#![feature(never_type)]
#![feature(hasher_prefixfree_extras)]
#![allow(clippy::uninlined_format_args)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]
#![cfg_attr(not(test), deny(clippy::expect_used))]
#![cfg_attr(not(test), deny(clippy::panic))]
#![cfg_attr(not(test), deny(clippy::todo))]
// #![cfg_attr(not(test), warn(clippy::unimplemented))]

pub mod parsing;
pub use parsing::*;
pub mod analysis;
pub mod common;
pub mod compiling;
pub use common::*;
pub mod ir;
pub mod name_resolution;
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
