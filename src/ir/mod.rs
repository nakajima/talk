include!(concat!(env!("OUT_DIR"), "/instr_impls.rs"));
pub mod basic_block;
pub mod function;
pub mod highlighter;
pub mod instruction;
pub mod interpreter;
pub mod io;
pub mod ir_error;
pub mod ir_parser;
pub mod ir_ty;
pub mod list;
pub mod lowerer;
pub mod monomorphizer;
pub mod program;
pub mod register;
pub mod terminator;
pub mod value;

#[cfg(test)]
pub mod lowerer_tests;
