use std::fmt::Display;
use std::sync::Arc;

use indexmap::IndexMap;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use sha2::{Digest, Sha256};
use tracing::instrument;

use crate::{
    compiling::driver::Exports,
    ir::{program::Program, value::RecordId},
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    types::{
        conformance::{ConformanceClaim, ConformanceEvidence, ConformanceKey},
        infer_ty::Ty,
        type_catalog::{MemberBinding, Nominal},
        types::{TypeEntry, Types},
    },
};

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

#[derive(Debug, Default)]
pub struct ModuleEnvironment {
    modules_by_name: FxHashMap<String, ModuleId>,
    modules_by_local: FxHashMap<ModuleId, StableModuleId>,
    modules: FxHashMap<StableModuleId, Arc<Module>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NamedSymbolKind {
    Struct,
    Enum,
    Protocol,
}

impl NamedSymbolKind {
    fn matches(self, symbol: Symbol) -> bool {
        matches!(
            (self, symbol),
            (Self::Struct, Symbol::Struct(..))
                | (Self::Enum, Symbol::Enum(..))
                | (Self::Protocol, Symbol::Protocol(..))
        )
    }
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

    pub fn lookup_named_symbol_in_module(
        &self,
        module_id: ModuleId,
        name: &str,
        kind: NamedSymbolKind,
    ) -> Option<Symbol> {
        let module = self.get_module(module_id)?;
        let mut matches: Vec<_> = module
            .symbol_names
            .iter()
            .filter_map(|(symbol, symbol_name)| {
                (symbol_name == name && kind.matches(*symbol)).then_some(*symbol)
            })
            .collect();
        matches.sort();
        matches.dedup();

        match matches.as_slice() {
            [symbol] => Some(*symbol),
            [] => None,
            _ => {
                tracing::warn!(
                    ?module_id,
                    ?kind,
                    name,
                    ?matches,
                    "ambiguous named symbol lookup"
                );
                None
            }
        }
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

    pub fn lookup_member_index(&self, receiver: &Symbol) -> Option<IndexMap<Label, MemberBinding>> {
        let module_id = receiver.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        module.types.catalog.member_index.get(receiver).cloned()
    }

    pub fn lookup_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        self.lookup_member_binding(receiver, label)
            .map(|binding| binding.symbol)
    }

    pub fn lookup_member_binding(&self, receiver: &Symbol, label: &Label) -> Option<MemberBinding> {
        let module_id = receiver.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_member \"{:?}.{}\" in {}",
            receiver,
            label,
            module.name
        );
        module.types.catalog.lookup_member_binding(receiver, label)
    }

    pub fn lookup_direct_member_binding(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<MemberBinding> {
        let module_id = receiver.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_direct_member \"{:?}.{}\" in {}",
            receiver,
            label,
            module.name
        );
        module
            .types
            .catalog
            .lookup_direct_member_binding(receiver, label)
    }

    pub fn lookup_constructor_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        let module_id = receiver.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_constructor_member \"{:?}.{}\" in {}",
            receiver,
            label,
            module.name
        );
        module
            .types
            .catalog
            .lookup_constructor_member(receiver, label)
    }

    pub fn lookup_direct_constructor_member(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        let module_id = receiver.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        tracing::trace!(
            "lookup_direct_constructor_member \"{:?}.{}\" in {}",
            receiver,
            label,
            module.name
        );
        module
            .types
            .catalog
            .lookup_direct_constructor_member(receiver, label)
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

    pub fn lookup_method_requirement(&self, protocol_id: &Symbol, label: &Label) -> Option<Symbol> {
        let module_id = protocol_id.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        module
            .types
            .catalog
            .lookup_method_requirement(protocol_id, label)
    }

    pub fn method_requirement_label(&self, method_req: &Symbol) -> Option<(Symbol, Label)> {
        if let Some(module_id) = method_req.external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
        {
            return module.types.catalog.method_requirement_label(method_req);
        }

        None
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

    #[instrument(skip(self))]
    pub fn lookup_conformance_claim(&self, key: &ConformanceKey) -> Option<ConformanceClaim> {
        if let Some(module_id) = key.conforming_id.external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
            && let Some(claim) = module.types.catalog.conformance_claims.get(key)
        {
            return Some(claim.clone());
        }

        if let Some(module_id) = Symbol::Protocol(key.protocol_id).external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
            && let Some(claim) = module.types.catalog.conformance_claims.get(key)
        {
            return Some(claim.clone());
        }

        None
    }

    #[instrument(skip(self))]
    pub fn lookup_conformance(&self, key: &ConformanceKey) -> Option<&ConformanceEvidence> {
        if let Some(module_id) = key.conforming_id.external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
        {
            return module.types.catalog.conformance_evidence.get(key);
        }

        if let Some(module_id) = Symbol::Protocol(key.protocol_id).external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
        {
            return module.types.catalog.conformance_evidence.get(key);
        }

        None
    }

    pub fn lookup_witness(
        &self,
        key: &ConformanceKey,
        label: &Label,
        method_req: &Symbol,
    ) -> Option<Symbol> {
        if let Some(module_id) = key.conforming_id.external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
            && let Some(witness) = module.types.catalog.lookup_witness(key, label, method_req)
        {
            return Some(witness);
        }

        if let Some(module_id) = Symbol::Protocol(key.protocol_id).external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
            && let Some(witness) = module.types.catalog.lookup_witness(key, label, method_req)
        {
            return Some(witness);
        }

        None
    }

    pub fn lookup_associated_type_witnesses(
        &self,
        key: &ConformanceKey,
    ) -> Option<FxHashMap<Label, Ty>> {
        if let Some(module_id) = key.conforming_id.external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
            && let Some(witnesses) = module.types.catalog.associated_type_witnesses(key)
        {
            return Some(witnesses);
        }

        if let Some(module_id) = Symbol::Protocol(key.protocol_id).external_module_id()
            && let Some(stable_id) = self.modules_by_local.get(&module_id)
            && let Some(module) = self.modules.get(stable_id)
            && let Some(witnesses) = module.types.catalog.associated_type_witnesses(key)
        {
            return Some(witnesses);
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
                    .conformance_evidence
                    .keys()
                    .filter(|k| k.protocol_id == *protocol_id),
            );
            acc
        })
    }

    /// Returns all conformance claims from all imported modules.
    pub fn all_conformance_claims(&self) -> Vec<(ConformanceKey, ConformanceClaim)> {
        self.modules
            .iter()
            .flat_map(|(_, module)| {
                module
                    .types
                    .catalog
                    .conformance_claims
                    .iter()
                    .map(|(k, v)| (*k, v.clone()))
            })
            .collect()
    }

    /// Returns all validated conformance evidence from all imported modules.
    pub fn all_conformance_evidence(&self) -> Vec<(ConformanceKey, ConformanceEvidence)> {
        self.modules
            .iter()
            .flat_map(|(_, module)| {
                module
                    .types
                    .catalog
                    .conformance_evidence
                    .iter()
                    .map(|(k, v)| (*k, v.clone()))
            })
            .collect()
    }

    pub fn lookup_nominal(&self, symbol: &Symbol) -> Option<&Nominal> {
        let module_id = symbol.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        module.types.catalog.nominals.get(symbol)
    }

    /// Lookup a global constant value from an external module
    pub fn lookup_global_constant(
        &self,
        symbol: &Symbol,
    ) -> Option<&crate::types::type_catalog::GlobalConstant> {
        let module_id = symbol.external_module_id()?;
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        module.types.catalog.global_constants.get(symbol)
    }

    pub fn imported_symbol_names(&self) -> FxHashMap<Symbol, String> {
        self.modules
            .values()
            .fold(FxHashMap::default(), |mut acc, module| {
                acc.extend(module.symbol_names.clone());
                acc
            })
    }

    pub fn imported_record_labels(&self) -> FxHashMap<RecordId, Vec<String>> {
        self.modules
            .values()
            .fold(FxHashMap::default(), |mut acc, module| {
                acc.extend(module.program.record_labels.clone());
                acc
            })
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

    pub fn program_for(&self, module_id: ModuleId) -> Option<&Program> {
        let stable_id = self.modules_by_local.get(&module_id)?;
        let module = self.modules.get(stable_id)?;
        Some(&module.program)
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
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
