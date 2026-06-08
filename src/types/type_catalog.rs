use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::{ModuleEnvironment, ModuleId},
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    types::{
        conformance::{ConformanceClaim, ConformanceEvidence, ConformanceKey, WitnessTable},
        infer_ty::Ty,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Nominal {
    pub properties: IndexMap<Label, Ty>,
    pub variants: IndexMap<Label, Vec<Ty>>,
    pub type_params: Vec<Ty>,
}

impl Nominal {
    pub fn import_as(self, module_id: ModuleId) -> Nominal {
        Nominal {
            properties: self
                .properties
                .into_iter()
                .map(|(k, v)| (k, v.import(module_id)))
                .collect(),
            variants: self
                .variants
                .into_iter()
                .map(|(k, v)| (k, v.into_iter().map(|v| v.import(module_id)).collect()))
                .collect(),
            type_params: self
                .type_params
                .into_iter()
                .map(|v| v.import(module_id))
                .collect(),
        }
    }

    pub fn substitutions(&self, type_args: &[Ty]) -> FxHashMap<Ty, Ty> {
        self.type_params
            .clone()
            .into_iter()
            .zip(type_args.iter().cloned())
            .collect()
    }

    pub fn substituted_variant_values(&self, type_args: &[Ty]) -> IndexMap<Label, Vec<Ty>> {
        let substitutions = self.substitutions(type_args);
        self.variants.clone().into_iter().fold(
            IndexMap::<Label, Vec<Ty>>::default(),
            |mut acc, (label, tys)| {
                let values = tys
                    .into_iter()
                    .map(|t| substitutions.get(&t).unwrap_or(&t).clone())
                    .collect();
                acc.insert(label, values);
                acc
            },
        )
    }

    pub fn substitute_properties(&self, type_args: &[Ty]) -> IndexMap<Label, Ty> {
        let substitutions = self.substitutions(type_args);
        self.properties.clone().into_iter().fold(
            IndexMap::<Label, Ty>::default(),
            |mut acc, (label, ty)| {
                let t = substitutions.get(&ty);
                acc.insert(label, t.unwrap_or(&ty).clone());
                acc
            },
        )
    }
}

/// Represents a global constant value that can be inlined at use sites
#[derive(Debug, PartialEq, Clone, serde::Serialize, serde::Deserialize)]
pub enum GlobalConstant {
    Int(i64),
    Float(f64),
    Bool(bool),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MemberSource {
    Property,
    InstanceMethod,
    Variant,
    MethodRequirement,
    Protocol(ProtocolId),
}

impl MemberSource {
    fn import_as(self, module_id: ModuleId) -> Self {
        match self {
            MemberSource::Property => MemberSource::Property,
            MemberSource::InstanceMethod => MemberSource::InstanceMethod,
            MemberSource::Variant => MemberSource::Variant,
            MemberSource::MethodRequirement => MemberSource::MethodRequirement,
            MemberSource::Protocol(protocol_id) => {
                MemberSource::Protocol(protocol_id.import(module_id))
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MemberBinding {
    pub symbol: Symbol,
    pub source: MemberSource,
}

impl MemberBinding {
    fn import_as(self, module_id: ModuleId) -> Self {
        Self {
            symbol: self.symbol.import(module_id),
            source: self.source.import_as(module_id),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ConstructorMemberSource {
    ChildType,
    StaticMethod,
    Member(MemberSource),
}

impl ConstructorMemberSource {
    fn import_as(self, module_id: ModuleId) -> Self {
        match self {
            ConstructorMemberSource::ChildType => ConstructorMemberSource::ChildType,
            ConstructorMemberSource::StaticMethod => ConstructorMemberSource::StaticMethod,
            ConstructorMemberSource::Member(source) => {
                ConstructorMemberSource::Member(source.import_as(module_id))
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ConstructorMemberBinding {
    pub symbol: Symbol,
    pub source: ConstructorMemberSource,
}

impl ConstructorMemberBinding {
    fn import_as(self, module_id: ModuleId) -> Self {
        Self {
            symbol: self.symbol.import(module_id),
            source: self.source.import_as(module_id),
        }
    }
}

/// Local type storage for one completed module.
///
/// Cross-module completed lookup is exposed by `Types`; solver-time raw lookup is
/// exposed by `TypeSession`. This catalog owns the local raw tables and the
/// materialized completed indexes they produce.
#[derive(Debug, PartialEq, Clone, serde::Serialize, serde::Deserialize, Default)]
pub struct TypeCatalog {
    pub nominals: IndexMap<Symbol, Nominal>,
    /// Declared conformance claims plus candidate witnesses from their bodies.
    pub conformance_claims: IndexMap<ConformanceKey, ConformanceClaim>,
    /// Validated conformance evidence consumed by projection, member, and specialization logic.
    pub conformance_evidence: IndexMap<ConformanceKey, ConformanceEvidence>,
    pub associated_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub extensions: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub child_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub initializers: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub properties: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub instance_methods: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub static_methods: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub variants: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub method_requirements: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    /// Materialized completed instance-member lookup, including direct and protocol-visible members.
    #[serde(default)]
    pub member_index: IndexMap<Symbol, IndexMap<Label, MemberBinding>>,
    /// Materialized completed type/constructor-receiver lookup.
    #[serde(default)]
    pub constructor_member_index: IndexMap<Symbol, IndexMap<Label, ConstructorMemberBinding>>,
    pub effects: IndexMap<Symbol, Ty>,
    /// Global constants (Int, Float, Bool) that can be inlined from external modules
    pub global_constants: FxHashMap<Symbol, GlobalConstant>,
}

impl TypeCatalog {
    pub(crate) fn declare_conformance(&mut self, claim: ConformanceClaim) {
        let key = claim.key();
        if let Some(existing) = self.conformance_claims.get_mut(&key) {
            existing.merge_candidates(claim);
        } else {
            self.conformance_claims.insert(key, claim);
        }
    }

    pub(crate) fn inherit_conformances(&mut self) -> Vec<ConformanceKey> {
        let mut inserted = vec![];

        loop {
            let existing_keys = self
                .conformance_evidence
                .keys()
                .copied()
                .collect::<Vec<_>>();
            let conformances = self
                .conformance_evidence
                .values()
                .cloned()
                .collect::<Vec<_>>();
            let mut changed = false;

            for conformance in &conformances {
                let protocol_symbol = Symbol::Protocol(conformance.protocol_id);
                for super_key in existing_keys
                    .iter()
                    .filter(|key| key.conforming_id == protocol_symbol)
                {
                    let inherited_key = ConformanceKey {
                        protocol_id: super_key.protocol_id,
                        conforming_id: conformance.conforming_id,
                    };
                    if self.conformance_evidence.contains_key(&inherited_key) {
                        continue;
                    }

                    self.conformance_evidence.insert(
                        inherited_key,
                        ConformanceEvidence::from_superprotocol(
                            conformance.node_id,
                            conformance.conforming_id,
                            super_key.protocol_id,
                            conformance.span,
                        ),
                    );
                    inserted.push(inherited_key);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        inserted
    }

    pub(crate) fn rebuild_member_index(&mut self, modules: &ModuleEnvironment) {
        self.member_index.clear();
        self.constructor_member_index.clear();
        self.materialize_direct_members();

        loop {
            let mut changed = false;

            let evidence_keys = self
                .conformance_evidence
                .keys()
                .copied()
                .collect::<Vec<_>>();
            for key in evidence_keys {
                changed |=
                    self.materialize_protocol_members(key.conforming_id, key.protocol_id, modules);
            }

            let superprotocol_claims = self
                .conformance_claims
                .keys()
                .filter(|key| matches!(key.conforming_id, Symbol::Protocol(_)))
                .copied()
                .collect::<Vec<_>>();
            for key in superprotocol_claims {
                changed |=
                    self.materialize_protocol_members(key.conforming_id, key.protocol_id, modules);
            }

            if !changed {
                break;
            }
        }

        self.materialize_constructor_members();
    }

    fn materialize_direct_members(&mut self) {
        let tables = [
            (&self.properties, MemberSource::Property),
            (&self.instance_methods, MemberSource::InstanceMethod),
            (&self.variants, MemberSource::Variant),
            (&self.method_requirements, MemberSource::MethodRequirement),
        ];

        let mut entries = vec![];
        for (table, source) in tables {
            for (receiver, members) in table {
                for (label, symbol) in members {
                    entries.push((*receiver, label.clone(), *symbol, source));
                }
            }
        }

        for (receiver, label, symbol, source) in entries {
            self.insert_member_binding(receiver, label, MemberBinding { symbol, source });
        }
    }

    fn materialize_protocol_members(
        &mut self,
        receiver: Symbol,
        protocol_id: ProtocolId,
        modules: &ModuleEnvironment,
    ) -> bool {
        let protocol_symbol = Symbol::Protocol(protocol_id);
        let mut bindings = self
            .member_index
            .get(&protocol_symbol)
            .cloned()
            .unwrap_or_default();
        if let Some(imported) = modules.lookup_member_index(&protocol_symbol) {
            bindings.extend(imported);
        }

        let mut changed = false;
        for (label, binding) in bindings {
            let source = match binding.source {
                MemberSource::Protocol(inherited_protocol_id) => {
                    MemberSource::Protocol(inherited_protocol_id)
                }
                MemberSource::Property
                | MemberSource::InstanceMethod
                | MemberSource::Variant
                | MemberSource::MethodRequirement => MemberSource::Protocol(protocol_id),
            };
            changed |= self.insert_member_binding(
                receiver,
                label,
                MemberBinding {
                    symbol: binding.symbol,
                    source,
                },
            );
        }

        changed
    }

    fn materialize_constructor_members(&mut self) {
        let child_types = self.child_types.clone();
        let static_methods = self.static_methods.clone();
        let variants = self.variants.clone();
        let instance_methods = self.instance_methods.clone();
        let method_requirements = self.method_requirements.clone();

        self.materialize_constructor_table(&child_types, ConstructorMemberSource::ChildType);
        self.materialize_constructor_table(&static_methods, ConstructorMemberSource::StaticMethod);
        self.materialize_constructor_table(
            &variants,
            ConstructorMemberSource::Member(MemberSource::Variant),
        );
        self.materialize_constructor_table(
            &instance_methods,
            ConstructorMemberSource::Member(MemberSource::InstanceMethod),
        );
        self.materialize_constructor_table(
            &method_requirements,
            ConstructorMemberSource::Member(MemberSource::MethodRequirement),
        );

        let protocol_members = self
            .member_index
            .iter()
            .flat_map(|(receiver, members)| {
                members.iter().filter_map(|(label, binding)| {
                    matches!(binding.source, MemberSource::Protocol(_)).then_some((
                        *receiver,
                        label.clone(),
                        ConstructorMemberBinding {
                            symbol: binding.symbol,
                            source: ConstructorMemberSource::Member(binding.source),
                        },
                    ))
                })
            })
            .collect::<Vec<_>>();

        for (receiver, label, binding) in protocol_members {
            self.insert_constructor_member_binding(receiver, label, binding);
        }
    }

    fn materialize_constructor_table(
        &mut self,
        table: &IndexMap<Symbol, IndexMap<Label, Symbol>>,
        source: ConstructorMemberSource,
    ) {
        let entries = table
            .iter()
            .flat_map(|(receiver, members)| {
                members.iter().map(|(label, symbol)| {
                    (
                        *receiver,
                        label.clone(),
                        ConstructorMemberBinding {
                            symbol: *symbol,
                            source,
                        },
                    )
                })
            })
            .collect::<Vec<_>>();

        for (receiver, label, binding) in entries {
            self.insert_constructor_member_binding(receiver, label, binding);
        }
    }

    fn insert_member_binding(
        &mut self,
        receiver: Symbol,
        label: Label,
        binding: MemberBinding,
    ) -> bool {
        let entries = self.member_index.entry(receiver).or_default();
        if entries.contains_key(&label) {
            return false;
        }

        entries.insert(label, binding);
        true
    }

    fn insert_constructor_member_binding(
        &mut self,
        receiver: Symbol,
        label: Label,
        binding: ConstructorMemberBinding,
    ) -> bool {
        let entries = self.constructor_member_index.entry(receiver).or_default();
        if entries.contains_key(&label) {
            return false;
        }

        entries.insert(label, binding);
        true
    }

    pub(crate) fn lookup_initializers(&self, receiver: &Symbol) -> Option<IndexMap<Label, Symbol>> {
        self.initializers.get(receiver).cloned()
    }

    pub(crate) fn lookup_constructor_member(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        self.lookup_constructor_member_binding(receiver, label)
            .map(|binding| binding.symbol)
    }

    fn lookup_constructor_member_binding(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<ConstructorMemberBinding> {
        self.constructor_member_index
            .get(receiver)
            .and_then(|entries| entries.get(label))
            .copied()
    }

    pub(crate) fn lookup_direct_constructor_member(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        if let Some(entries) = self.child_types.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some(*sym);
        }

        if let Some(entries) = self.static_methods.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some(*sym);
        }

        if let Some(entries) = self.variants.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some(*sym);
        }

        if let Some(entries) = self.instance_methods.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some(*sym);
        }

        if let Some(entries) = self.method_requirements.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some(*sym);
        }

        None
    }

    pub(crate) fn lookup_direct_member_binding(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<MemberBinding> {
        if let Some(entries) = self.properties.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some(MemberBinding {
                symbol: *sym,
                source: MemberSource::Property,
            });
        }

        if let Some(entries) = self.instance_methods.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some(MemberBinding {
                symbol: *sym,
                source: MemberSource::InstanceMethod,
            });
        }

        if let Some(entries) = self.variants.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some(MemberBinding {
                symbol: *sym,
                source: MemberSource::Variant,
            });
        }

        if let Some(entries) = self.method_requirements.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some(MemberBinding {
                symbol: *sym,
                source: MemberSource::MethodRequirement,
            });
        }

        None
    }

    /// Looks up completed member visibility from the materialized index.
    pub(crate) fn lookup_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        self.lookup_member_binding(receiver, label)
            .map(|binding| binding.symbol)
    }

    pub(crate) fn lookup_member_binding(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<MemberBinding> {
        self.member_index
            .get(receiver)
            .and_then(|entries| entries.get(label))
            .copied()
    }

    pub(crate) fn lookup_method_requirement(
        &self,
        protocol_sym: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        self.method_requirements
            .get(protocol_sym)
            .and_then(|entries| entries.get(label))
            .copied()
    }

    pub(crate) fn method_requirement_label(&self, method_req: &Symbol) -> Option<(Symbol, Label)> {
        for (protocol_sym, entries) in &self.method_requirements {
            for (label, sym) in entries {
                if sym == method_req {
                    return Some((*protocol_sym, label.clone()));
                }
            }
        }
        None
    }

    pub(crate) fn lookup_witness(
        &self,
        key: &ConformanceKey,
        label: &Label,
        method_req: &Symbol,
    ) -> Option<Symbol> {
        self.conformance_evidence
            .get(key)
            .and_then(|conformance| conformance.witnesses.get_witness(label, method_req))
    }

    pub(crate) fn associated_type_witnesses(
        &self,
        key: &ConformanceKey,
    ) -> Option<FxHashMap<Label, Ty>> {
        self.conformance_evidence
            .get(key)
            .map(|conformance| conformance.witnesses.associated_types.clone())
    }

    pub(crate) fn lookup_effect(&self, id: &Symbol) -> Option<Ty> {
        self.effects.get(id).cloned()
    }

    pub(crate) fn import_as(self, module_id: ModuleId) -> TypeCatalog {
        TypeCatalog {
            nominals: self
                .nominals
                .into_iter()
                .map(|(k, v)| (k.import(module_id), v.import_as(module_id)))
                .collect(),
            conformance_claims: self
                .conformance_claims
                .into_iter()
                .map(|(k, v)| {
                    (
                        ConformanceKey {
                            protocol_id: k.protocol_id.import(module_id),
                            conforming_id: k.conforming_id.import(module_id),
                        },
                        v.import_as(module_id),
                    )
                })
                .collect(),
            conformance_evidence: self
                .conformance_evidence
                .into_iter()
                .map(|(k, v)| {
                    (
                        ConformanceKey {
                            protocol_id: k.protocol_id.import(module_id),
                            conforming_id: k.conforming_id.import(module_id),
                        },
                        ConformanceEvidence {
                            node_id: v.node_id,
                            conforming_id: v.conforming_id.import(module_id),
                            protocol_id: v.protocol_id.import(module_id),
                            origin: v.origin,
                            witnesses: WitnessTable {
                                methods: import_mapped(v.witnesses.methods, module_id),
                                associated_types: v
                                    .witnesses
                                    .associated_types
                                    .into_iter()
                                    .map(|(k, v)| (k, v.import(module_id)))
                                    .collect(),
                                requirements: import_symbol_mapped(
                                    v.witnesses.requirements,
                                    module_id,
                                ),
                            },
                            span: v.span,
                        },
                    )
                })
                .collect(),
            associated_types: import_nominal_mapped(self.associated_types, module_id),
            extensions: import_nominal_mapped(self.extensions, module_id),
            child_types: import_nominal_mapped(self.child_types, module_id),
            initializers: import_nominal_mapped(self.initializers, module_id),
            properties: import_nominal_mapped(self.properties, module_id),
            instance_methods: import_nominal_mapped(self.instance_methods, module_id),
            static_methods: import_nominal_mapped(self.static_methods, module_id),
            variants: import_nominal_mapped(self.variants, module_id),
            method_requirements: import_nominal_mapped(self.method_requirements, module_id),
            member_index: import_member_index(self.member_index, module_id),
            constructor_member_index: import_constructor_member_index(
                self.constructor_member_index,
                module_id,
            ),
            effects: self
                .effects
                .into_iter()
                .map(|(k, v)| (k.import(module_id), v.import(module_id)))
                .collect(),
            global_constants: self
                .global_constants
                .into_iter()
                .map(|(k, v)| (k.import(module_id), v))
                .collect(),
        }
    }
}

fn import_constructor_member_index(
    mapping: IndexMap<Symbol, IndexMap<Label, ConstructorMemberBinding>>,
    module_id: ModuleId,
) -> IndexMap<Symbol, IndexMap<Label, ConstructorMemberBinding>> {
    mapping
        .into_iter()
        .map(|(key, value)| {
            let key = key.import(module_id);
            let value = value
                .into_iter()
                .map(|(k, v)| (k, v.import_as(module_id)))
                .collect();
            (key, value)
        })
        .collect()
}

fn import_member_index(
    mapping: IndexMap<Symbol, IndexMap<Label, MemberBinding>>,
    module_id: ModuleId,
) -> IndexMap<Symbol, IndexMap<Label, MemberBinding>> {
    mapping
        .into_iter()
        .map(|(key, value)| {
            let key = key.import(module_id);
            let value = value
                .into_iter()
                .map(|(k, v)| (k, v.import_as(module_id)))
                .collect();
            (key, value)
        })
        .collect()
}

fn import_mapped(
    mapping: FxHashMap<Label, Symbol>,
    module_id: ModuleId,
) -> FxHashMap<Label, Symbol> {
    mapping
        .into_iter()
        .map(|(k, v)| (k, v.import(module_id)))
        .collect()
}

fn import_symbol_mapped(
    mapping: FxHashMap<Symbol, Symbol>,
    module_id: ModuleId,
) -> FxHashMap<Symbol, Symbol> {
    mapping
        .into_iter()
        .map(|(k, v)| (k.import(module_id), v.import(module_id)))
        .collect()
}

fn import_nominal_mapped(
    mapping: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    module_id: ModuleId,
) -> IndexMap<Symbol, IndexMap<Label, Symbol>> {
    mapping
        .into_iter()
        .map(|(key, value)| {
            let key = key.import(module_id);
            let value = value
                .into_iter()
                .map(|(k, v)| (k, v.import(module_id)))
                .collect();
            (key, value)
        })
        .collect()
}
