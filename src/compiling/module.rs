use indexmap::IndexMap;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use sha2::{Digest, Sha256};
use std::fmt::Display;
use tracing::instrument;

use crate::{
    compiling::driver::Exports,
    ir::program::Program,
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    types::{
        conformance::{Conformance, ConformanceKey},
        ty::Ty,
        type_catalog::Nominal,
        type_session::{TypeEntry, Types},
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
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

#[derive(Debug, Default)]
pub struct ModuleEnvironment {
    modules_by_name: FxHashMap<String, ModuleId>,
    modules_by_local: FxHashMap<ModuleId, StableModuleId>,
    modules: FxHashMap<StableModuleId, Module>,
}

impl ModuleEnvironment {
    pub fn lookup_name(&self, name: &str) -> Vec<Symbol> {
        self.modules
            .iter()
            .filter_map(|m| m.1.exports.get(name).copied())
            .collect()
    }

    pub fn resolve_name(&self, sym: &Symbol) -> Option<&String> {
        let module_id = sym.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!("resolve_name \"{}\" in {}", sym, module.name);
        module.symbol_names.get(sym)
    }

    pub fn lookup(&self, symbol: &Symbol) -> Option<TypeEntry> {
        let module_id = symbol.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!("lookup \"{}\" in {}", symbol, module.name);
        module.types.get_symbol(symbol).cloned()
    }

    pub fn lookup_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        let module_id = receiver.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_member \"{:?}.{}\" in {}",
            receiver,
            label,
            module.name
        );
        module
            .types
            .catalog
            .lookup_member(receiver, label)
            .map(|m| m.0)
    }

    pub fn lookup_static_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        let module_id = receiver.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_static_member \"{:?}.{}\" in {}",
            receiver,
            label,
            module.name
        );
        module.types.catalog.lookup_static_member(receiver, label)
    }

    pub fn lookup_initializers(&self, receiver: &Symbol) -> Option<IndexMap<Label, Symbol>> {
        let module_id = receiver.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!("lookup_initializers \"{:?}\" in {}", receiver, module.name);
        module.types.catalog.lookup_initializers(receiver)
    }

    pub fn lookup_effect(&self, id: &Symbol) -> Option<Ty> {
        let module_id = id.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!("lookup_effect \"{:?}\" in {}", id, module.name);
        module.types.catalog.lookup_effect(id)
    }

    pub fn lookup_associated_types(&self, protocol_id: &Symbol) -> Option<IndexMap<Label, Symbol>> {
        let module_id = protocol_id.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_associated_types \"{:?}\" in {}",
            protocol_id,
            module.name
        );
        module
            .types
            .catalog
            .associated_types
            .get(protocol_id)
            .cloned()
    }

    pub fn lookup_method_requirements(
        &self,
        protocol_id: &Symbol,
    ) -> Option<IndexMap<Label, Symbol>> {
        let module_id = protocol_id.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_method_requirements \"{:?}\" in {}",
            protocol_id,
            module.name
        );
        module
            .types
            .catalog
            .method_requirements
            .get(protocol_id)
            .cloned()
    }

    pub fn lookup_instance_methods(&self, symbol: &Symbol) -> Option<IndexMap<Label, Symbol>> {
        let module_id = symbol.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_instance_methods \"{:?}\" in {}",
            symbol,
            module.name
        );
        module.types.catalog.instance_methods.get(symbol).cloned()
    }

    pub fn lookup_concrete_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        let module_id = receiver.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_concrete_member \"{:?}.{}\" in {}",
            receiver,
            label,
            module.name
        );
        module
            .types
            .catalog
            .lookup_concrete_member(receiver, label)
            .map(|m| m.0)
    }

    #[instrument(skip(self))]
    pub fn lookup_conformance(&self, key: &ConformanceKey) -> Option<&Conformance<Ty>> {
        if let Some(module_id) = key.conforming_id.external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
        {
            return module.types.catalog.conformances.get(key);
        }

        if let Some(module_id) = Symbol::Protocol(key.protocol_id).external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
        {
            return module.types.catalog.conformances.get(key);
        }

        None
    }

    pub fn lookup_protocol_conformances(&self, protocol_id: &ProtocolId) -> Vec<ConformanceKey> {
        self.modules.iter().fold(vec![], |mut acc, module| {
            acc.extend(
                module
                    .1
                    .types
                    .catalog
                    .conformances
                    .keys()
                    .filter(|k| k.protocol_id == *protocol_id),
            );
            acc
        })
    }

    /// Returns all conformances from all imported modules
    pub fn all_conformances(&self) -> Vec<(ConformanceKey, Conformance<Ty>)> {
        self.modules
            .iter()
            .flat_map(|(_, module)| {
                module
                    .types
                    .catalog
                    .conformances
                    .iter()
                    .map(|(k, v)| (*k, v.clone()))
            })
            .collect()
    }

    pub fn lookup_nominal(&self, symbol: &Symbol) -> Option<&Nominal<Ty>> {
        let module_id = symbol.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        module.types.catalog.nominals.get(symbol)
    }

    pub fn imported_symbol_names(&self) -> FxHashMap<Symbol, String> {
        self.modules
            .values()
            .fold(FxHashMap::default(), |mut acc, module| {
                acc.extend(module.symbol_names.clone());
                acc
            })
    }

    pub fn import_core(&mut self, module: Module) {
        self.modules_by_local.insert(ModuleId::Core, module.id);
        self.modules_by_name.insert("Core".into(), ModuleId::Core);
        self.modules.insert(module.id, module);
    }

    pub fn import(&mut self, module: Module) -> ModuleId {
        let id = ModuleId::External(self.modules.len() as u16);
        self.modules_by_local.insert(id, module.id);
        self.modules_by_name.insert(module.name.clone(), id);
        self.modules.insert(module.id, module.import_as(id));
        id
    }

    pub fn program_for(&self, module_id: ModuleId) -> Option<&Program> {
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        Some(&module.program)
    }
}

#[derive(Debug, Clone)]
pub struct Module {
    pub id: StableModuleId,
    pub name: String,
    pub types: Types,
    pub symbol_names: FxHashMap<Symbol, String>,
    pub exports: IndexMap<String, Symbol>,
    pub program: Program,
}

impl Module {
    pub fn import_as(self, module_id: ModuleId) -> Module {
        Self {
            id: self.id,
            name: self.name,
            types: self.types.import_as(module_id),
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
            program: self.program,
        }
    }
}
