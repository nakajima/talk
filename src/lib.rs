#![feature(box_patterns)]
#![feature(associated_type_defaults)]
#![feature(assert_matches)]
#![feature(iter_advance_by)]
#![feature(if_let_guard)]
#![cfg_attr(not(test), warn(clippy::unwrap_used))]
#![cfg_attr(not(test), warn(clippy::expect_used))]
#![cfg_attr(not(test), warn(clippy::panic))]
#![cfg_attr(not(test), warn(clippy::todo))]
#![cfg_attr(not(test), warn(clippy::unimplemented))]

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
pub mod prelude;

#[cfg(test)]
#[ctor::ctor]
fn init_logger() {
    // .is_test(true) silences the “already initialized” panic
    let _ = env_logger::builder()
        .format_timestamp(None)
        .format_target(false)
        .is_test(true)
        .try_init();
}

pub mod test_utils;
