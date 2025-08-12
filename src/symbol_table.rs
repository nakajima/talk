use std::{
    collections::{BTreeMap, HashMap},
    path::PathBuf,
};

use crate::{compiling::compiled_module::ImportedSymbol, parsing::expr_id::ExprID, span::Span};

#[derive(Default, Copy, Clone, Eq, PartialOrd, Ord)]
pub struct SymbolID(pub i32);

impl std::fmt::Debug for SymbolID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.0)
    }
}

impl std::hash::Hash for SymbolID {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

#[cfg(test)]
impl PartialEq for SymbolID {
    fn eq(&self, other: &Self) -> bool {
        if other.0 == SymbolID::ANY.0 || self.0 == SymbolID::ANY.0 {
            true
        } else {
            other.0 == self.0
        }
    }
}

#[cfg(not(test))]
impl PartialEq for SymbolID {
    fn eq(&self, other: &Self) -> bool {
        other.0 == self.0
    }
}

impl SymbolID {
    #[cfg(test)]
    pub const ANY: SymbolID = SymbolID(i32::MIN + 2);

    pub const INT: SymbolID = SymbolID(-1);
    pub const FLOAT: SymbolID = SymbolID(-2);
    pub const BOOL: SymbolID = SymbolID(-3);
    pub const POINTER: SymbolID = SymbolID(-4);
    pub const TUPLE: SymbolID = SymbolID(-10);
    pub const RECORD: SymbolID = SymbolID(-11);

    // These are special because they have syntactic sugar that gets handled
    // by the compiler. If we change the prelude, we may need to change some of them.
    // We can see them by running:
    //
    // $ SHOW_BUILTIN_SYMBOLS=1 cargo test -- --nocapture
    pub const ARRAY: SymbolID = SymbolID(41);
    pub const OPTIONAL: SymbolID = SymbolID(37);
    pub const STRING: SymbolID = SymbolID(56);
    pub const ADD: SymbolID = SymbolID(1);
    pub const SUBTRACT: SymbolID = SymbolID(6);
    pub const MULTIPLY: SymbolID = SymbolID(11);
    pub const DIVIDE: SymbolID = SymbolID(16);

    // These are special for the lowering phase
    pub const GENERATED_MAIN: SymbolID = SymbolID(i32::MIN);
    pub const ENV: SymbolID = SymbolID(i32::MIN + 1);

    // Remove the prelude's symbol offset
    pub fn resolved(index: i32) -> SymbolID {
        SymbolID(index + crate::prelude::compile_prelude().symbols.max_id())
    }

    // Remove the prelude's symbol offset
    pub fn typed(index: i32) -> SymbolID {
        SymbolID(index + crate::prelude::compile_prelude().symbols.max_id())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    Self_,
    FuncDef,
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
    StaticProperty,
    Protocol,
    RecordLabel,
    Import(ImportedSymbol),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Definition {
    pub path: PathBuf,
    pub line: u32,
    pub col: u32,
    pub sym: Option<SymbolID>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemberKind {
    Initializer,
    Method,
    StaticProperty,
    StaticMethod,
    Property,
    Generic,
    EnumVariant,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemberSymbol {
    pub name: String,
    pub member_id: SymbolID,
    pub expr_id: ExprID,
    pub kind: MemberKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymbolInfo {
    pub name: String,
    pub kind: SymbolKind,
    pub expr_id: ExprID,
    pub is_captured: bool,
    pub definition: Option<Definition>,
    pub documentation: Option<String>,
}

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct TypeTable {
    pub members: Vec<MemberSymbol>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolTable {
    symbols: BTreeMap<SymbolID, SymbolInfo>,
    next_id: i32,
    pub types: BTreeMap<SymbolID, Vec<MemberSymbol>>,
    pub symbol_map: BTreeMap<Span, SymbolID>,
    pub import_symbol_map: HashMap<SymbolID, SymbolID>,
}

impl SymbolTable {
    pub fn base() -> Self {
        let mut table = Self {
            symbols: Default::default(),
            next_id: Default::default(),
            types: Default::default(),
            symbol_map: Default::default(),
            import_symbol_map: Default::default(),
        };

        crate::builtins::import_symbols(&mut table);

        table
    }

    pub fn find_imported(&self, imported: &SymbolID) -> Option<&SymbolID> {
        self.import_symbol_map.get(imported)
    }

    pub fn add_map(&mut self, span: Span, symbol_id: &SymbolID) {
        self.symbol_map.insert(span, *symbol_id);
    }

    pub fn import(&mut self, symbol_id: &SymbolID, info: SymbolInfo) {
        self.symbols.insert(*symbol_id, info);
    }

    pub fn members_for(&self, symbol_id: &SymbolID, kind: MemberKind) -> Vec<&MemberSymbol> {
        self.types
            .get(symbol_id)
            .map(|t| t.iter().filter(|t| t.kind == kind).collect())
            .unwrap_or_default()
    }

    pub fn initializers_for(&self, symbol_id: &SymbolID) -> Vec<&ExprID> {
        self.types
            .get(symbol_id)
            .map(|t| {
                t.iter()
                    .filter_map(|t| {
                        if t.kind == MemberKind::Initializer {
                            Some(&t.expr_id)
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    pub fn member_kind(&self, type_id: &SymbolID, name: &str) -> Option<&MemberSymbol> {
        self.types
            .get(type_id)
            .and_then(|t| t.iter().find(|t| t.name == name))
    }

    pub fn properties_for(&self, symbol_id: &SymbolID) -> Vec<&MemberSymbol> {
        self.types
            .get(symbol_id)
            .map(|t| {
                t.iter()
                    .filter(|t| t.kind == MemberKind::Property)
                    .collect()
            })
            .unwrap_or_default()
    }

    pub fn methods_for(&self, symbol_id: &SymbolID) -> Vec<&ExprID> {
        self.types
            .get(symbol_id)
            .map(|t| {
                t.iter()
                    .filter_map(|t| {
                        if t.kind == MemberKind::Method {
                            Some(&t.expr_id)
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    pub fn all(&self) -> BTreeMap<SymbolID, SymbolInfo> {
        self.symbols.clone()
    }

    pub fn max_id(&self) -> i32 {
        self.next_id
    }

    pub fn mark_as_captured(&mut self, symbol_id: &SymbolID) {
        if let Some(info) = self.symbols.get_mut(symbol_id)
            && symbol_id.0 > 0
        {
            info.is_captured = true;
        }
    }

    pub fn add(
        &mut self,
        name: &str,
        kind: SymbolKind,
        expr_id: ExprID,
        definition: Option<Definition>,
    ) -> SymbolID {
        tracing::trace!(
            "add symbol {:?} {:?} {:?} {:?}",
            name,
            kind,
            expr_id,
            definition,
        );

        tracing::info!("add symbol: {name} next_id: {}", self.next_id);

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
                documentation: None,
            },
        );

        symbol_id
    }

    pub fn map_import(&mut self, theirs: SymbolID, ours: SymbolID) {
        self.import_symbol_map.insert(theirs, ours);
    }

    pub fn add_property(
        &mut self,
        type_id: SymbolID,
        name: String,
        expr_id: ExprID,
        member_id: SymbolID,
        is_static: bool,
    ) {
        self.types.entry(type_id).or_default().push(MemberSymbol {
            name,
            member_id,
            kind: if is_static {
                MemberKind::StaticProperty
            } else {
                MemberKind::Property
            },
            expr_id,
        });
    }

    pub fn add_method(
        &mut self,
        type_id: SymbolID,
        name: String,
        expr_id: ExprID,
        member_id: SymbolID,
        is_static: bool,
    ) {
        self.types.entry(type_id).or_default().push(MemberSymbol {
            name,
            member_id,
            kind: if is_static {
                MemberKind::StaticMethod
            } else {
                MemberKind::Method
            },
            expr_id,
        });
    }

    pub fn add_generic(
        &mut self,
        type_id: SymbolID,
        name: String,
        expr_id: ExprID,
        member_id: SymbolID,
    ) {
        self.types.entry(type_id).or_default().push(MemberSymbol {
            name,
            member_id,
            kind: MemberKind::Generic,
            expr_id,
        });
    }

    pub fn add_enum_variant(
        &mut self,
        type_id: SymbolID,
        name: String,
        expr_id: ExprID,
        member_id: SymbolID,
    ) {
        self.types.entry(type_id).or_default().push(MemberSymbol {
            name,
            member_id,
            kind: MemberKind::EnumVariant,
            expr_id,
        });
    }

    pub fn add_initializer(
        &mut self,
        type_id: SymbolID,
        name: String,
        expr_id: ExprID,
        member_id: SymbolID,
    ) {
        self.types.entry(type_id).or_default().push(MemberSymbol {
            name,
            member_id,
            kind: MemberKind::Initializer,
            expr_id,
        });
    }

    pub fn initializer_for(&self, struct_id: &SymbolID) -> Option<ExprID> {
        self.types.get(struct_id).and_then(|table| {
            table.iter().find_map(|t| {
                if t.kind == MemberKind::Initializer {
                    Some(t.expr_id)
                } else {
                    None
                }
            })
        })
    }

    pub fn lookup(&self, name: &str) -> Option<SymbolID> {
        for (id, info) in &self.symbols {
            if info.name == name {
                return Some(*id);
            }
        }

        None
    }

    pub fn get(&self, symbol_id: &SymbolID) -> Option<&SymbolInfo> {
        self.symbols.get(symbol_id)
    }

    pub fn get_mut(&mut self, symbol_id: &SymbolID) -> Option<&mut SymbolInfo> {
        self.symbols.get_mut(symbol_id)
    }
}
