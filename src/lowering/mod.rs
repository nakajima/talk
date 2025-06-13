include!(concat!(env!("OUT_DIR"), "/instr_impls.rs"));
pub mod builtins;
pub mod instr;
pub mod ir_module;
pub mod ir_printer;
pub mod ir_type;
pub mod lowerer;
pub mod parsing;
pub mod register;
