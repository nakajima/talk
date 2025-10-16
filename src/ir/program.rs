use indexmap::IndexMap;

use crate::{
    ir::{function::Function, ir_ty::IrTy},
    label::Label,
    name_resolution::symbol::Symbol,
};

#[derive(Debug, Default, PartialEq)]
pub struct Program {
    pub functions: IndexMap<Symbol, Function<IrTy, Label>>,
}

impl Program {
    pub fn entrypoint(&self) -> Option<&Function<IrTy, Label>> {
        for (sym, func) in self.functions.iter() {
            if func.name.name_str() == "main"
                && matches!(sym, Symbol::Global(..) | Symbol::Synthesized(..))
            {
                return Some(func);
            }
        }

        None
    }
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
