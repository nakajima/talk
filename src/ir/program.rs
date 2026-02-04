use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    ir::{
        function::Function,
        ir_ty::IrTy,
        lowerer::{PolyFunction, StaticMemory},
        value::RecordId,
    },
    name_resolution::symbol::Symbol,
};

#[derive(Debug, Clone, Default, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Program {
    pub functions: IndexMap<Symbol, Function<IrTy>>,
    pub polyfunctions: IndexMap<Symbol, PolyFunction>,
    pub static_memory: StaticMemory,
    pub record_labels: FxHashMap<RecordId, Vec<String>>,
}

impl Program {
    pub fn entrypoint(&self) -> Option<&Function<IrTy>> {
        for func in self.functions.values() {
            if matches!(func.name, Symbol::Main) {
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
