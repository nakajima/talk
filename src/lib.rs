pub mod builtins;
pub use builtins::*;
pub mod source_file;
pub use source_file::*;
pub mod symbol_table;
pub use symbol_table::*;
pub mod lexing;
pub use lexing::*;
pub mod analysis;
pub use analysis::*;
pub mod parsing;
pub use parsing::*;
pub mod lowering;
pub use lowering::*;
pub mod prelude;

#[cfg(test)]
#[ctor::ctor]
fn init_logger() {
    // .is_test(true) silences the “already initialized” panic
    let _ = env_logger::builder().is_test(true).try_init();
}

#[cfg(test)]
pub mod test_utils;
