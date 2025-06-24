include!(concat!(env!("OUT_DIR"), "/instr_impls.rs"));
pub mod builtins;
pub mod instr;
pub mod ir_error;
pub mod ir_function;
pub mod ir_module;
pub mod ir_printer;
pub mod ir_type;
pub mod ir_value;
pub mod lowerer;
#[cfg(test)]
mod lowerer_tests;
pub mod parsing;
pub mod phi_predecessors;
pub mod register;
