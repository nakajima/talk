use std::collections::HashMap;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SymbolID(pub u32);

#[derive(Debug, Clone)]
pub enum SymbolKind {
    Func,
    Param,
    Local,
}

#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: String,
    pub kind: SymbolKind,
}

#[derive(Default, Clone, Debug)]
pub struct SymbolTable {
    symbols: HashMap<SymbolID, SymbolInfo>,
    next_id: u32,
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
}
