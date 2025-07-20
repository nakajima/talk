use std::collections::{BTreeMap, HashMap};

use crate::{SymbolID, expr_id::ExprID, lowering::ir_module::IRModule, ty::Ty, type_defs::TypeDef};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ImportedSymbolKind {
    Function { index: usize },
    Constant { index: usize },
    Type,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExportedSymbol {
    pub module: String,
    pub expr_id: ExprID,
    pub name: String,
    pub symbol: SymbolID,
    pub kind: ImportedSymbolKind,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CompiledModule {
    pub module_name: String,
    pub symbols: HashMap<String, ExportedSymbol>,
    pub typed_symbols: HashMap<SymbolID, Ty>,
    pub types: BTreeMap<SymbolID, TypeDef>,
    pub ir_module: IRModule,
}

#[cfg(test)]
pub fn compile_module(name: impl Into<String>, code: &str) -> CompiledModule {
    use std::path::PathBuf;

    use crate::compiling::driver::{Driver, DriverConfig};

    let mut driver = Driver::new(
        name,
        DriverConfig {
            executable: false,
            include_prelude: false,
            include_comments: false,
        },
    );

    driver.update_file(&PathBuf::from("-"), code);
    driver.compile_modules().unwrap().first().unwrap().clone()
}
