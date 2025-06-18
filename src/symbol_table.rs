use std::{collections::HashMap, path::PathBuf};

use crate::{Phase, SourceFile, parser::ExprID, prelude::compile_prelude, span::Span};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SymbolID(pub i32);

impl SymbolID {
    // These are special because they have syntactic sugar that gets handled
    // by the compiler.
    pub const OPTIONAL: SymbolID = SymbolID(1);
    pub const ARRAY: SymbolID = SymbolID(3);

    // These are special for the lowering phase
    pub const GENERATED_MAIN: SymbolID = SymbolID(i32::MIN);
    pub const ENV: SymbolID = SymbolID(i32::MIN + 1);

    // Remove the prelude's symbol offset
    pub fn resolved(index: i32) -> SymbolID {
        SymbolID(index + compile_prelude().symbols.max_id())
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
    SyntheticConstructor,
    Property,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Definition {
    pub path: PathBuf,
    pub line: u32,
    pub col: u32,
}

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct PropertyInfo {
    pub name: String,
    pub type_id: Option<ExprID>,
    pub default_value_id: Option<ExprID>,
}

#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: String,
    pub kind: SymbolKind,
    pub expr_id: ExprID,
    pub is_captured: bool,
    pub definition: Option<Definition>,
}

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct TypeTable {
    pub properties: Vec<PropertyInfo>,
    pub initializers: Vec<ExprID>,
}

#[derive(Clone, Debug)]
pub struct SymbolTable {
    symbols: HashMap<SymbolID, SymbolInfo>,
    next_id: i32,
    pub types: HashMap<SymbolID, TypeTable>,
    pub symbol_map: HashMap<Span, SymbolID>,
}

impl SymbolTable {
    pub fn base() -> Self {
        let mut table = Self {
            symbols: Default::default(),
            next_id: Default::default(),
            types: Default::default(),
            symbol_map: Default::default(),
        };

        crate::builtins::import_symbols(&mut table);

        table
    }

    pub fn add_map<P: Phase>(
        &mut self,
        source_file: &SourceFile<P>,
        node_id: &ExprID,
        symbol_id: &SymbolID,
    ) {
        let span = source_file.span(node_id);
        self.symbol_map.insert(span, *symbol_id);
    }

    pub fn import(&mut self, symbol_id: &SymbolID, info: SymbolInfo) {
        self.symbols.insert(*symbol_id, info);
    }

    pub fn initializers_for(&self, symbol_id: &SymbolID) -> Option<&Vec<ExprID>> {
        self.types.get(symbol_id).map(|t| &t.initializers)
    }

    pub fn properties_for(&self, symbol_id: &SymbolID) -> Option<&Vec<PropertyInfo>> {
        self.types.get(symbol_id).map(|t| &t.properties)
    }

    pub fn with_prelude(prelude_symbols: &HashMap<SymbolID, SymbolInfo>) -> Self {
        let mut table = Self::base();

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
        if let Some(info) = self.symbols.get_mut(symbol_id) {
            info.is_captured = true;
        }
    }

    #[track_caller]
    pub fn add(
        &mut self,
        name: &str,
        kind: SymbolKind,
        expr_id: ExprID,
        definition: Option<Definition>,
    ) -> SymbolID {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "add symbol {:?} {:?} {:?} {:?} from {}:{}",
                name,
                kind,
                expr_id,
                definition,
                loc.file(),
                loc.line()
            );
        }

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
        let info = PropertyInfo {
            name,
            type_id,
            default_value_id,
        };

        if let Some(table) = self.types.get_mut(&to_symbol_id) {
            table.properties.push(info);
        } else {
            let table = TypeTable {
                initializers: vec![],
                properties: vec![info],
            };

            self.types.insert(to_symbol_id, table);
        }
    }

    pub fn add_initializer(&mut self, to_symbol_id: SymbolID, id: ExprID) {
        if let Some(table) = self.types.get_mut(&to_symbol_id) {
            table.initializers.push(id);
        } else {
            let table = TypeTable {
                initializers: vec![id],
                properties: vec![],
            };

            self.types.insert(to_symbol_id, table);
        }
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
