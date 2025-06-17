#![feature(box_patterns)]

pub mod builtins;
pub use builtins::*;
pub mod source_file;
pub use source_file::*;
pub mod symbol_table;
pub use symbol_table::*;
// pub mod file_store;
// pub use file_store::*;
pub mod lexing;
pub use lexing::*;
pub mod type_checking;
pub use type_checking::*;
pub mod parsing;
pub use parsing::*;
pub mod compiling;
pub mod diagnostic;
pub mod interpreter;
pub mod lowering;

#[cfg(feature = "cli")]
pub mod lsp;
pub mod prelude;

#[cfg(test)]
#[ctor::ctor]
fn init_logger() {
    // .is_test(true) silences the “already initialized” panic
    let _ = env_logger::builder().is_test(true).try_init();
}

#[cfg(test)]
pub mod test_utils;
