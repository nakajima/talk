use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        conformance::{Conformance, ConformanceKey, Witnesses},
        infer_row::{Row, RowParamId},
        infer_ty::Ty,
        type_operations::UnificationSubstitutions,
        type_session::{MemberSource, TypeSession},
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
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
        self.variants
            .clone()
            .into_iter()
            .fold(IndexMap::<Label, Vec<Ty>>::default(), |mut acc, (label, tys)| {
                let values = tys
                    .into_iter()
                    .map(|t| substitutions.get(&t).unwrap_or(&t).clone())
                    .collect();
                acc.insert(label, values);
                acc
            })
    }

    pub fn substitute_properties(&self, type_args: &[Ty]) -> IndexMap<Label, Ty> {
        let substitutions = self.substitutions(type_args);
        self.properties
            .clone()
            .into_iter()
            .fold(IndexMap::<Label, Ty>::default(), |mut acc, (label, ty)| {
                let t = substitutions.get(&ty);
                acc.insert(label, t.unwrap_or(&ty).clone());
                acc
            })
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TrackedInstantiations {
    pub ty: FxHashMap<NodeID, FxHashMap<Symbol, Ty>>,
    pub row: FxHashMap<NodeID, FxHashMap<RowParamId, Row>>,
}

impl TrackedInstantiations {
    pub fn apply(
        mut self,
        session: &mut TypeSession,
        substitutions: &mut UnificationSubstitutions,
    ) -> Self {
        let ty = std::mem::take(&mut self.ty);
        let row = std::mem::take(&mut self.row);

        let mut instantiations = TrackedInstantiations::default();
        for (id, entries) in ty {
            for (param, ty) in entries {
                instantiations
                    .ty
                    .entry(id)
                    .or_default()
                    .insert(param, session.apply(ty, substitutions));
            }
        }
        for (id, entries) in row {
            for (param, row) in entries {
                instantiations
                    .row
                    .entry(id)
                    .or_default()
                    .insert(param, session.apply_row(row, substitutions));
            }
        }

        instantiations
    }

    pub fn insert_ty(&mut self, id: NodeID, param: Symbol, ty: Ty) {
        self.ty.entry(id).or_default().insert(param, ty);
    }

    pub fn insert_row(&mut self, id: NodeID, param: RowParamId, ty: Row) {
        self.row.entry(id).or_default().insert(param, ty);
    }
}

impl Default for TrackedInstantiations {
    fn default() -> Self {
        Self {
            ty: Default::default(),
            row: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeCatalog {
    pub nominals: IndexMap<Symbol, Nominal>,
    pub conformances: IndexMap<ConformanceKey, Conformance>,
    pub associated_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub extensions: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub child_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub initializers: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub properties: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub instance_methods: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub static_methods: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub variants: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub method_requirements: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub instantiations: TrackedInstantiations,
    pub effects: IndexMap<Symbol, Ty>,
}

impl Default for TypeCatalog {
    fn default() -> Self {
        Self {
            nominals: Default::default(),
            conformances: Default::default(),
            extensions: Default::default(),
            child_types: Default::default(),
            associated_types: Default::default(),

            initializers: Default::default(),
            properties: Default::default(),
            instance_methods: Default::default(),
            static_methods: Default::default(),
            variants: Default::default(),
            method_requirements: Default::default(),

            instantiations: Default::default(),
            effects: Default::default(),
        }
    }
}

impl TypeCatalog {
    pub fn lookup_initializers(&self, receiver: &Symbol) -> Option<IndexMap<Label, Symbol>> {
        self.initializers.get(receiver).cloned()
    }

    pub fn lookup_static_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
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

    pub fn lookup_member(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<(Symbol, MemberSource)> {
        if let Some(entries) = self.properties.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some((*sym, MemberSource::SelfMember));
        }

        if let Some(entries) = self.instance_methods.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some((*sym, MemberSource::SelfMember));
        }

        if let Some(entries) = self.variants.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some((*sym, MemberSource::SelfMember));
        }

        if let Some(entries) = self.method_requirements.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some((*sym, MemberSource::SelfMember));
        }

        for ConformanceKey {
            protocol_id,
            conforming_id,
        } in self.conformances.keys()
        {
            if conforming_id != receiver {
                continue;
            }

            if let Some((member, _)) = self.lookup_member(&protocol_id.into(), label) {
                return Some((member, MemberSource::Protocol(*protocol_id)));
            }
        }

        None
    }

    pub fn protocol_for_method_requirement(&self, method_req: &Symbol) -> Option<Symbol> {
        for (protocol_sym, entries) in &self.method_requirements {
            for (_, sym) in entries {
                if sym == method_req {
                    return Some(*protocol_sym);
                }
            }
        }
        None
    }

    pub fn lookup_effect(&self, id: &Symbol) -> Option<Ty> {
        self.effects.get(id).cloned()
    }

    pub fn lookup_concrete_member(
        &self,
        receiver: &Symbol,
        label: &Label,
    ) -> Option<(Symbol, MemberSource)> {
        if let Some(entries) = self.properties.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some((*sym, MemberSource::SelfMember));
        }

        if let Some(entries) = self.instance_methods.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some((*sym, MemberSource::SelfMember));
        }

        if let Some(entries) = self.variants.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some((*sym, MemberSource::SelfMember));
        }

        if let Some(entries) = self.method_requirements.get(receiver)
            && let Some(sym) = entries.get(label)
        {
            return Some((*sym, MemberSource::SelfMember));
        }

        None
    }

    pub fn instance_methods_for(&self, receiver: &Symbol) -> IndexMap<Label, Symbol> {
        self.instance_methods
            .get(receiver)
            .cloned()
            .unwrap_or_default()
    }

    pub fn import_as(self, module_id: ModuleId) -> TypeCatalog {
        TypeCatalog {
            nominals: self
                .nominals
                .into_iter()
                .map(|(k, v)| (k.import(module_id), v.import_as(module_id)))
                .collect(),
            conformances: self
                .conformances
                .into_iter()
                .map(|(k, v)| {
                    (
                        ConformanceKey {
                            protocol_id: k.protocol_id.import(module_id),
                            conforming_id: k.conforming_id.import(module_id),
                        },
                        Conformance {
                            node_id: v.node_id,
                            conforming_id: v.conforming_id.import(module_id),
                            protocol_id: v.protocol_id.import(module_id),
                            witnesses: Witnesses {
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
            instantiations: TrackedInstantiations {
                ty: self
                    .instantiations
                    .ty
                    .into_iter()
                    .map(|(k, v)| {
                        (
                            k,
                            v.into_iter()
                                .map(|(k, v)| (k, v.import(module_id)))
                                .collect(),
                        )
                    })
                    .collect(),
                row: self
                    .instantiations
                    .row
                    .into_iter()
                    .map(|(k, v)| {
                        (
                            k,
                            v.into_iter()
                                .map(|(k, v)| (k, v.import(module_id)))
                                .collect(),
                        )
                    })
                    .collect(),
            },
            effects: self
                .effects
                .into_iter()
                .map(|(k, v)| (k.import(module_id), v.import(module_id)))
                .collect(),
        }
    }
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
