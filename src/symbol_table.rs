use std::collections::HashMap;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SymbolID(pub i32);

#[derive(Debug, Clone)]
pub enum SymbolKind {
    Func,
    Param,
    Local,
    Enum,
    EnumVariant(SymbolID),
}

#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: String,
    pub kind: SymbolKind,
}

#[derive(Default, Clone, Debug)]
pub struct SymbolTable {
    symbols: HashMap<SymbolID, SymbolInfo>,
    next_id: i32,
}

impl SymbolTable {
    pub fn add(&mut self, name: &str, kind: SymbolKind) -> SymbolID {
        self.next_id += 1;
        let symbol_id = SymbolID(self.next_id);
        self.symbols.insert(
            symbol_id,
            SymbolInfo {
                name: name.to_string(),
                kind,
            },
        );

        symbol_id
    }

    pub fn get(&self, symbol_id: &SymbolID) -> Option<&SymbolInfo> {
        self.symbols.get(symbol_id)
    }
}
