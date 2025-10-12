use rustc_hash::FxHashMap;

use crate::{
    ir::{function::Function, ir_ty::IrTy},
    label::Label,
    name_resolution::symbol::Symbol,
};

#[derive(Debug, Default, PartialEq)]
pub struct Program {
    pub functions: FxHashMap<Symbol, Function<IrTy, Label>>,
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        for func in self.functions.values() {
            parts.push(format!("{func}"));
        }
        write!(f, "{}", parts.join("\n\n"))
    }
}
