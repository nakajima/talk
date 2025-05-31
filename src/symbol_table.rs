use std::collections::HashMap;

use crate::{
    parser::ExprID,
    type_checker::{Scheme, Ty},
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SymbolID(pub i32);

#[derive(Debug, Clone)]
pub enum SymbolKind {
    Func,
    Param,
    Local,
    Enum,
    EnumVariant(SymbolID),
    BuiltinType,
    CustomType,
    TypeParameter,
    PatternBind,
}

#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: String,
    pub kind: SymbolKind,
    pub expr_id: ExprID,
}

#[derive(Clone, Debug)]
pub struct SymbolTable {
    symbols: HashMap<SymbolID, SymbolInfo>,
    next_id: i32,
}

impl Default for SymbolTable {
    fn default() -> Self {
        let mut table = Self {
            symbols: Default::default(),
            next_id: Default::default(),
        };

        table.symbols.insert(
            SymbolID(-1),
            SymbolInfo {
                name: "Int".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: -1,
            },
        );

        table.symbols.insert(
            SymbolID(-2),
            SymbolInfo {
                name: "Float".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: -2,
            },
        );

        table
    }
}

impl SymbolTable {
    pub fn default_env_scope() -> HashMap<SymbolID, Scheme> {
        let mut scope = HashMap::new();
        scope.insert(SymbolID(-1), Scheme::new(Ty::Int, vec![]));
        scope.insert(SymbolID(-2), Scheme::new(Ty::Float, vec![]));
        scope
    }

    pub fn default_name_scope() -> HashMap<String, SymbolID> {
        let mut scope = HashMap::new();
        scope.insert("Int".to_string(), SymbolID(-1));
        scope.insert("Float".to_string(), SymbolID(-2));
        scope
    }

    pub fn add(&mut self, name: &str, kind: SymbolKind, expr_id: ExprID) -> SymbolID {
        self.next_id += 1;
        let symbol_id = SymbolID(self.next_id);
        self.symbols.insert(
            symbol_id,
            SymbolInfo {
                name: name.to_string(),
                kind,
                expr_id,
            },
        );

        symbol_id
    }

    pub fn lookup(&self, name: &str) -> Option<SymbolID> {
        log::warn!("Lookup: {:?}", name);
        for (id, info) in &self.symbols {
            log::warn!("Looking up: {:?}, {:?}", id, info);
            if info.name == name {
                return Some(*id);
            }
        }

        None
    }

    pub fn get(&self, symbol_id: &SymbolID) -> Option<&SymbolInfo> {
        self.symbols.get(symbol_id)
    }
}
