use std::collections::HashMap;

use crate::{SymbolID, lowering::ir_module::IRModule, ty::Ty};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ImportedSymbolKind {
    Function { index: usize },
    Constant { index: usize },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ImportedSymbol {
    pub module: String,
    pub name: String,
    pub symbol: SymbolID,
    pub kind: ImportedSymbolKind,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CompiledModule {
    pub module_name: String,
    pub symbols: HashMap<String, ImportedSymbol>,
    pub types: HashMap<SymbolID, Ty>,
    pub ir_module: IRModule,
}
