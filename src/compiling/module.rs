use std::cell::RefCell;
use std::fmt::Display;
use std::rc::Rc;
use std::sync::Arc;

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
    /// Stable module identity includes full exported callable names
    /// (ADR 0041), not only base-name keys: an overload set changing
    /// shape changes the module's interface.
    pub fn generate(
        name: &str,
        exports: &Exports,
        contracts: &rustc_hash::FxHashMap<Symbol, crate::types::callables::CallableContract>,
        procedural_macro_exports: &[String],
    ) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(name.as_bytes());
        hasher.update([0]);
        for (key, set) in exports {
            hasher.update(key.as_bytes());
            for symbol in set {
                if let Some(contract) = contracts.get(symbol) {
                    hasher.update([1]);
                    hasher.update(contract.name.to_string().as_bytes());
                }
            }
            hasher.update([0]);
        }
        for name in procedural_macro_exports {
            hasher.update(b"macro\0");
            hasher.update(name.as_bytes());
            hasher.update([0]);
        }
        Self(hasher.finalize().into())
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
    /// The module stamp for the program under compilation when its
    /// config assigns no other id (absolute identity, ADR 0038).
    pub const Main: ModuleId = ModuleId(u16::MAX);
    pub const fn External(i: u16) -> ModuleId {
        ModuleId(i + 2)
    }
    /// The reserved well-known band, descending below `Main`: fixed ids
    /// for the closed set of bundled modules (stdlib), so their symbols
    /// mint absolutely and every session registers them at the same ids
    /// without colliding with sequentially assigned ones.
    pub const fn WellKnown(i: u16) -> ModuleId {
        ModuleId(u16::MAX - 1 - i)
    }
    /// Sequential session assignment never reaches this floor.
    pub(crate) const WELL_KNOWN_FLOOR: u16 = u16::MAX - 1024;

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

/// Session-wide module numbering (ADR 0038 identity repair): one local
/// id per stable module identity, assigned at first sight and shared by
/// every environment cloned from the session's first (clones share the
/// registry, maps stay per-environment views). "One module = one id" is
/// structural, so no downstream consumer unifies spellings.
#[derive(Debug)]
pub struct ModuleRegistry {
    by_stable: FxHashMap<StableModuleId, ModuleId>,
    next: u16,
}

impl Default for ModuleRegistry {
    fn default() -> Self {
        Self {
            by_stable: FxHashMap::default(),
            next: ModuleId::External(0).0,
        }
    }
}

impl ModuleRegistry {
    /// Mint a fresh session id with no stable identity yet (package
    /// graphs assign ids before their modules compile); `bind` attaches
    /// the identity once the compiled module exists.
    fn reserve(&mut self) -> ModuleId {
        let id = ModuleId(self.next);
        self.next = self
            .next
            .checked_add(1)
            .expect("session module ids exhausted");
        id
    }

    /// Attach a stable identity to a pre-assigned id. One module, one
    /// id: rebinding to a different id is a session-numbering bug.
    fn bind(&mut self, stable: StableModuleId, id: ModuleId) -> Result<(), String> {
        match self.by_stable.get(&stable) {
            Some(&bound) if bound != id => Err(format!(
                "module {stable} is already numbered {bound} in this session (got {id})"
            )),
            Some(_) => Ok(()),
            None => {
                self.by_stable.insert(stable, id);
                // Well-known-band and Main ids never advance the
                // sequential counter.
                if id.0 >= self.next && id.0 < ModuleId::WELL_KNOWN_FLOOR {
                    self.next = id.0.checked_add(1).expect("session module ids exhausted");
                }
                Ok(())
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ModuleEnvironment {
    /// Shared across every environment of one compile session.
    registry: Rc<RefCell<ModuleRegistry>>,
    modules_by_name: FxHashMap<String, ModuleId>,
    modules_by_local: FxHashMap<ModuleId, StableModuleId>,
    modules: FxHashMap<StableModuleId, Arc<Module>>,
}

impl ModuleEnvironment {
    pub fn lookup_name(&self, name: &str) -> Vec<Symbol> {
        let mut matches: Vec<_> = self
            .modules
            .iter()
            .flat_map(|m| m.1.exports.get(name).cloned().unwrap_or_default())
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
        self.registry
            .borrow_mut()
            .bind(module.id, ModuleId::Core)
            .expect("core binds first in a session");
        self.modules_by_local.insert(ModuleId::Core, module.id);
        self.modules_by_name.insert("Core".into(), ModuleId::Core);
        self.modules.insert(module.id, module);
    }

    /// Register a module that was compiled with `module_id` already assigned.
    /// Package compilation reserves one id per package in the session's
    /// registry, so its typed body and exported interface keep the same
    /// cross-module ids everywhere in the session.
    pub fn import_compiled(&mut self, module: Module, module_id: ModuleId) -> Result<(), String> {
        if self.modules_by_local.contains_key(&module_id) {
            return Err(format!("module id {module_id} is already registered"));
        }
        if self.modules_by_name.contains_key(&module.name) {
            return Err(format!("module name {} is already registered", module.name));
        }
        self.registry.borrow_mut().bind(module.id, module_id)?;
        self.modules_by_local.insert(module_id, module.id);
        self.modules_by_name.insert(module.name.clone(), module_id);
        self.modules.insert(module.id, Arc::new(module));
        Ok(())
    }

    /// Mint a fresh session id for a module that has not compiled yet
    /// (`import_compiled` binds its identity afterwards).
    pub fn reserve_module_id(&self) -> ModuleId {
        self.registry.borrow_mut().reserve()
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
    pub exports: Exports,
    #[serde(default)]
    pub types: ModuleTypes,
    #[serde(default)]
    pub procedural_macros: Option<crate::procedural_macros::ProceduralMacroArtifact>,
}

impl Module {
    pub fn with_procedural_macros(
        mut self,
        artifact: Option<crate::procedural_macros::ProceduralMacroArtifact>,
    ) -> Self {
        let names = artifact
            .as_ref()
            .map(|artifact| {
                artifact
                    .exported_names()
                    .map(str::to_string)
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        self.id = StableModuleId::generate(
            &self.name,
            &self.exports,
            &self.types.catalog.callable_contracts,
            &names,
        );
        self.procedural_macros = artifact;
        self
    }
}
