use std::collections::HashMap;

use crate::{SymbolID, lowering::ir_function::IRFunction, ty::Ty};

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
pub struct ImportedModule {
    pub module_name: String,
    pub symbols: HashMap<String, ImportedSymbol>,
    pub types: HashMap<SymbolID, Ty>,
    pub functions: Vec<IRFunction>,
}
