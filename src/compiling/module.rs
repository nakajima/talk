use std::fmt::Display;
use std::sync::Arc;

use indexmap::IndexMap;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use sha2::{Digest, Sha256};

use crate::{compiling::driver::Exports, name_resolution::symbol::Symbol};

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct StableModuleId([u8; 32]);

impl Display for StableModuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.iter().map(|b| format!("{b:#x}")).join(""))
    }
}

impl StableModuleId {
    pub fn generate(exports: &Exports) -> Self {
        let hash = Sha256::digest(exports.keys().join("\n").as_bytes());
        Self(hash.into())
    }
}

#[derive(
    Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default, serde::Serialize, serde::Deserialize,
)]
pub struct ModuleId(pub u16);

#[allow(non_snake_case, non_upper_case_globals)]
impl ModuleId {
    pub const Current: ModuleId = ModuleId(0);
    pub const Core: ModuleId = ModuleId(1);
    pub const fn External(i: u16) -> ModuleId {
        ModuleId(i + 2)
    }

    pub fn is_external_or_core(&self) -> bool {
        self.0 > 0
    }

    pub fn is_external(&self) -> bool {
        self.0 > 1
    }
}

impl Display for ModuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::Core => write!(f, "C"),
            Self::Current => write!(f, "_"),
            id => write!(f, "{}", id.0),
        }
    }
}

impl std::fmt::Debug for ModuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::Core => write!(f, "C"),
            Self::Current => write!(f, "_"),
            id => write!(f, "{}", id.0),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ModuleEnvironment {
    modules_by_name: FxHashMap<String, ModuleId>,
    modules_by_local: FxHashMap<ModuleId, StableModuleId>,
    modules: FxHashMap<StableModuleId, Arc<Module>>,
}

impl ModuleEnvironment {
    pub fn lookup_name(&self, name: &str) -> Vec<Symbol> {
        let mut matches: Vec<_> = self
            .modules
            .iter()
            .filter_map(|m| m.1.exports.get(name).copied())
            .collect();
        matches.sort();
        matches
    }

    /// Get a reference to a module by its local module ID
    pub fn get_module(&self, module_id: ModuleId) -> Option<&Module> {
        let stable_id = self.modules_by_local.get(&module_id)?;
        self.modules.get(stable_id).map(|arc| arc.as_ref())
    }

    /// Get a reference to a module by its name
    pub fn get_module_by_name(&self, name: &str) -> Option<&Module> {
        let module_id = self.modules_by_name.get(name)?;
        self.get_module(*module_id)
    }

    /// Get the local module ID assigned to an imported module name.
    pub fn get_module_id_by_name(&self, name: &str) -> Option<ModuleId> {
        self.modules_by_name.get(name).copied()
    }

    pub fn imported_symbol_names(&self) -> FxHashMap<Symbol, String> {
        self.modules
            .values()
            .fold(FxHashMap::default(), |mut acc, module| {
                acc.extend(module.symbol_names.clone());
                acc
            })
    }

    /// Iterate every imported module (Phase 0 of type checking seeds its
    /// catalog and schemes from these).
    pub fn all_modules(&self) -> impl Iterator<Item = &Module> {
        self.modules.values().map(|arc| arc.as_ref())
    }

    pub fn import_core(&mut self, module: Arc<Module>) {
        self.modules_by_local.insert(ModuleId::Core, module.id);
        self.modules_by_name.insert("Core".into(), ModuleId::Core);
        self.modules.insert(module.id, module);
    }

    pub fn import(&mut self, module: Module) -> ModuleId {
        let id = ModuleId::External(self.modules.len() as u16);
        self.modules_by_local.insert(id, module.id);
        self.modules_by_name.insert(module.name.clone(), id);
        self.modules
            .insert(module.id, Arc::new(module.import_as(id)));
        id
    }
}

/// The type-system payload a compiled module carries: finished schemes for
/// its binders and its slice of the type catalog (nominals, protocols,
/// conformances, effects). The importing checker merges these in Phase 0.
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct ModuleTypes {
    pub schemes: FxHashMap<Symbol, crate::types::ty::Scheme>,
    pub catalog: crate::types::catalog::TypeCatalog,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Module {
    pub id: StableModuleId,
    pub name: String,
    pub symbol_names: FxHashMap<Symbol, String>,
    pub exports: IndexMap<String, Symbol>,
    #[serde(default)]
    pub types: ModuleTypes,
}

impl Module {
    pub fn import_as(self, module_id: ModuleId) -> Module {
        Self {
            id: self.id,
            name: self.name,
            symbol_names: self
                .symbol_names
                .into_iter()
                .map(|(k, v)| (k.import(module_id), v))
                .collect(),
            exports: self
                .exports
                .into_iter()
                .map(|(k, v)| (k, v.import(module_id)))
                .collect(),
            types: ModuleTypes {
                schemes: self
                    .types
                    .schemes
                    .into_iter()
                    .map(|(symbol, scheme)| {
                        (symbol.import(module_id), scheme.import_symbols(module_id))
                    })
                    .collect(),
                catalog: self.types.catalog.import_as(module_id),
            },
        }
    }
}
