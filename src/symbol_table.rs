use std::collections::HashMap;

use crate::{
    FileID,
    parser::ExprID,
    prelude::{compile_prelude, compile_prelude_for_name_resolver},
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SymbolID(pub i32);

impl SymbolID {
    pub const OPTIONAL: SymbolID = SymbolID(1);
    pub const ARRAY: SymbolID = SymbolID(-4);
    pub const GENERATED_MAIN: SymbolID = SymbolID(i32::MIN);

    // Remove the prelude's symbol offset
    pub fn resolved(index: i32) -> SymbolID {
        SymbolID(index + compile_prelude_for_name_resolver().symbols.max_id())
    }

    // Remove the prelude's symbol offset
    pub fn typed(index: i32) -> SymbolID {
        SymbolID(index + compile_prelude().symbols.max_id())
    }
}

#[derive(Debug, Clone)]
pub enum SymbolKind {
    Func,
    Param,
    Local,
    Enum,
    EnumVariant(SymbolID),
    Struct,
    BuiltinType,
    BuiltinFunc,
    CustomType,
    TypeParameter,
    PatternBind,
    VariantConstructor,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Definition {
    pub file_id: FileID,
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone)]
pub struct PropertyInfo {
    name: String,
    type_id: Option<ExprID>,
    default_value_id: Option<ExprID>
}

#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: String,
    pub kind: SymbolKind,
    pub expr_id: ExprID,
    pub is_captured: bool,
    pub definition: Option<Definition>,
    pub properties: Vec<PropertyInfo>,
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

        crate::builtins::import_symbols(&mut table);

        table
    }
}

impl SymbolTable {
    pub fn import(&mut self, symbol_id: &SymbolID, info: SymbolInfo) {
        self.symbols.insert(*symbol_id, info);
    }

    pub fn with_prelude(prelude_symbols: &HashMap<SymbolID, SymbolInfo>) -> Self {
        let mut table = Self::default();

        // Import all prelude symbols
        for (id, info) in prelude_symbols {
            table.symbols.insert(*id, info.clone());
        }

        // Set next_id to avoid collisions
        let max_id = prelude_symbols
            .keys()
            .filter(|id| id.0 > 0) // Only positive IDs
            .map(|id| id.0)
            .max()
            .unwrap_or(0);

        table.next_id = max_id + 1;
        table
    }

    // Convert symbols to initial name scope
    pub fn build_name_scope(&self) -> HashMap<String, SymbolID> {
        let mut scope = crate::builtins::default_name_scope(); // Builtins like Int, Float

        // Add all symbols to name->id mapping
        for (id, info) in &self.symbols {
            scope.insert(info.name.to_string(), *id);
        }

        scope
    }

    pub fn all(&self) -> HashMap<SymbolID, SymbolInfo> {
        self.symbols.clone()
    }

    pub fn max_id(&self) -> i32 {
        self.next_id
    }

    pub fn mark_as_captured(&mut self, symbol_id: &SymbolID) {
        self.symbols.get_mut(symbol_id).unwrap().is_captured = true;
    }

    pub fn add(
        &mut self,
        name: &str,
        kind: SymbolKind,
        expr_id: ExprID,
        definition: Option<Definition>,
    ) -> SymbolID {
        self.next_id += 1;
        let symbol_id = SymbolID(self.next_id);
        self.symbols.insert(
            symbol_id,
            SymbolInfo {
                name: name.to_string(),
                kind,
                expr_id,
                is_captured: false,
                definition,
                properties: vec![],
            },
        );

        symbol_id
    }

    pub fn add_property(
        &mut self,
        to_symbol_id: SymbolID,
        name: String,
        type_id: Option<ExprID>,
        default_value_id: Option<ExprID>,
    ) {
        self.symbols.get_mut(&to_symbol_id).map(|s| {
            s.properties.push(PropertyInfo {
                name,
                type_id,
                default_value_id,
            })
        });
    }

    pub fn lookup(&self, name: &str) -> Option<SymbolID> {
        log::warn!("Lookup: {name:?}");
        for (id, info) in &self.symbols {
            log::warn!("Looking up: {id:?}, {info:?}");
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
