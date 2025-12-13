use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        conformance::{Conformance, ConformanceKey, Witnesses},
        infer_row::RowParamId,
        infer_ty::{InferTy, TypeParamId},
        ty::{SomeType, Ty},
        type_session::{MemberSource, TypeEntry, TypeSession},
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Nominal<T: SomeType> {
    pub properties: IndexMap<Label, T>,
    pub variants: IndexMap<Label, Vec<T>>,
    pub type_params: Vec<T>,
}

impl Nominal<Ty> {
    pub fn import_as(self, module_id: ModuleId) -> Nominal<Ty> {
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
}

impl<T: SomeType> Nominal<T> {
    pub fn substitutions(&self, type_args: &[T]) -> FxHashMap<T, T> {
        self.type_params
            .clone()
            .into_iter()
            .zip(type_args.iter().cloned())
            .collect()
    }

    pub fn substituted_variant_values(&self, type_args: &[T]) -> IndexMap<Label, Vec<T>> {
        let substitutions = self.substitutions(type_args);
        self.variants.clone().into_iter().fold(
            IndexMap::<Label, Vec<T>>::default(),
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

    pub fn substitute_properties(&self, type_args: &[T]) -> IndexMap<Label, T> {
        let substitutions = self.substitutions(type_args);
        self.properties.clone().into_iter().fold(
            IndexMap::<Label, T>::default(),
            |mut acc, (label, ty)| {
                let t = substitutions.get(&ty);
                acc.insert(label, t.unwrap_or(&ty).clone());
                acc
            },
        )
    }
}

impl From<Nominal<Ty>> for Nominal<InferTy> {
    fn from(value: Nominal<Ty>) -> Self {
        Nominal::<InferTy> {
            properties: value
                .properties
                .into_iter()
                .map(|(label, ty)| (label, ty.into()))
                .collect(),
            variants: value
                .variants
                .into_iter()
                .map(|(label, tys)| (label, tys.into_iter().map(|t| t.into()).collect()))
                .collect(),
            type_params: value.type_params.into_iter().map(|ty| ty.into()).collect(),
        }
    }
}

impl From<Nominal<InferTy>> for Nominal<Ty> {
    fn from(value: Nominal<InferTy>) -> Self {
        Nominal::<Ty> {
            properties: value
                .properties
                .into_iter()
                .map(|(label, ty)| (label, ty.into()))
                .collect(),
            variants: value
                .variants
                .into_iter()
                .map(|(label, tys)| (label, tys.into_iter().map(|t| t.into()).collect()))
                .collect(),
            type_params: value.type_params.into_iter().map(|ty| ty.into()).collect(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TrackedInstantiations<T: SomeType> {
    pub ty: FxHashMap<(NodeID, TypeParamId), T>,
    pub row: FxHashMap<(NodeID, RowParamId), T::RowType>,
}

impl<T: SomeType> Default for TrackedInstantiations<T> {
    fn default() -> Self {
        Self {
            ty: Default::default(),
            row: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeCatalog<T: SomeType> {
    pub nominals: IndexMap<Symbol, Nominal<T>>,
    pub conformances: IndexMap<ConformanceKey, Conformance<T>>,
    pub associated_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub extensions: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub child_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub initializers: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub properties: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub instance_methods: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub static_methods: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub variants: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub method_requirements: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub instantiations: TrackedInstantiations<T>,
}

impl<T: SomeType> Default for TypeCatalog<T> {
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
        }
    }
}

impl TypeCatalog<InferTy> {
    pub fn finalize(self, session: &mut TypeSession) -> TypeCatalog<Ty> {
        let mut instantiations = TrackedInstantiations::default();
        for (key, infer_ty) in self.instantiations.ty {
            let ty = match session.finalize_ty(infer_ty) {
                TypeEntry::Mono(ty) => ty.clone(),
                TypeEntry::Poly(scheme) => scheme.ty.clone(),
            };
            instantiations.ty.insert(key, ty);
        }
        for (key, infer_row) in self.instantiations.row {
            instantiations
                .row
                .insert(key, session.finalize_row(infer_row));
        }
        TypeCatalog {
            nominals: self
                .nominals
                .into_iter()
                .map(|(k, v)| (k, v.into()))
                .collect(),
            associated_types: self.associated_types,
            conformances: self
                .conformances
                .into_iter()
                .map(|(k, v)| (k, v.finalize(session)))
                .collect(),
            extensions: self.extensions,
            child_types: self.child_types,
            initializers: self.initializers,
            properties: self.properties,
            instance_methods: self.instance_methods,
            static_methods: self.static_methods,
            variants: self.variants,
            method_requirements: self.method_requirements,
            instantiations,
        }
    }
}

impl<T: SomeType> TypeCatalog<T> {
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

    /// Look up the label for a method requirement symbol by searching all protocols
    pub fn method_requirement_label(&self, method_req: &Symbol) -> Option<Label> {
        for entries in self.method_requirements.values() {
            for (label, sym) in entries {
                if sym == method_req {
                    return Some(label.clone());
                }
            }
        }
        None
    }
}

impl TypeCatalog<Ty> {
    pub fn import_as(self, module_id: ModuleId) -> TypeCatalog<Ty> {
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
                            witnesses: Witnesses::<Ty> {
                                methods: import_mapped(v.witnesses.methods, module_id),
                                associated_types: v
                                    .witnesses
                                    .associated_types
                                    .into_iter()
                                    .map(|(k, v)| (k, v.import(module_id)))
                                    .collect(),
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
                    .map(|(k, v)| (k, v.import(module_id)))
                    .collect(),
                row: self
                    .instantiations
                    .row
                    .into_iter()
                    .map(|(k, v)| (k, v.import(module_id)))
                    .collect(),
            },
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
