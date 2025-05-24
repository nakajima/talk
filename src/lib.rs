pub mod program;
pub use program::*;
pub mod lexing;
pub use lexing::*;
pub mod analysis;
pub use analysis::*;
pub mod parsing;
pub use parsing::*;
pub mod lowering;
pub use lowering::*;

#[cfg(test)]
#[ctor::ctor]
fn init_logger() {
    // .is_test(true) silences the “already initialized” panic
    let _ = env_logger::builder().is_test(true).try_init();
}
