#![feature(box_patterns)]
#![feature(associated_type_defaults)]
#![feature(assert_matches)]
#![feature(iter_advance_by)]
#![feature(if_let_guard)]
#![feature(hash_set_entry)]
#![feature(slice_pattern)]
#![cfg_attr(not(test), warn(clippy::unwrap_used))]
#![cfg_attr(not(test), warn(clippy::expect_used))]
#![cfg_attr(not(test), warn(clippy::panic))]
#![cfg_attr(not(test), warn(clippy::todo))]
#![cfg_attr(not(test), warn(clippy::unimplemented))]

pub mod prelude;

pub mod builtins;
pub use builtins::*;
pub mod source_file;
pub use source_file::*;
pub mod symbol_table;
pub use symbol_table::*;
pub mod lexing;
pub use lexing::*;
pub mod type_checking;
pub use type_checking::*;
pub mod parsing;
pub use parsing::*;
pub mod analysis;
pub mod compiling;
pub mod diagnostic;
pub mod interpret;
pub mod lowering;
pub mod transforms;

#[cfg(feature = "cli")]
pub mod lsp;

#[cfg(test)]
pub mod test_utils;

#[cfg(test)]
#[ctor::ctor]
pub fn init_tracing() {
    test_utils::trace::init()
}
