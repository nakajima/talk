include!(concat!(env!("OUT_DIR"), "/instr_impls.rs"));
pub mod instr;
pub mod interpreter;
pub mod ir_module;
pub mod ir_printer;
pub mod lowerer;
pub mod parser;
