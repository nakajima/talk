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

    /// Merge static memory from an imported module's program.
    /// Appends the imported static memory after the current static memory
    /// and offsets all RawPtr values in imported functions.
    pub fn merge_static_memory(
        &mut self,
        imported: &Program,
        imported_symbols: &[Symbol],
    ) {
        if imported.static_memory.data.is_empty() {
            return;
        }

        let offset = self.static_memory.data.len();
        self.static_memory
            .data
            .extend_from_slice(&imported.static_memory.data);

        for sym in imported_symbols {
            if let Some(func) = self.functions.get_mut(sym) {
                for block in &mut func.blocks {
                    for instr in &mut block.instructions {
                        instr.offset_ptrs(offset);
                    }
                }
            }
        }
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
