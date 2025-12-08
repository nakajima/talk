use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        conformance::{Conformance, ConformanceKey},
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
pub enum MemberWitness<T> {
    Concrete(Symbol),
    Requirement(Symbol, T),
    Meta {
        receiver: T,
        label: Label,
    },
    /// Call to a default protocol method - needs conformance context for resolving
    /// internal method requirement calls
    DefaultMethod {
        method: Symbol,
        conformance: ConformanceKey,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeCatalog<T: SomeType> {
    pub nominals: FxHashMap<Symbol, Nominal<T>>,
    pub conformances: FxHashMap<ConformanceKey, Conformance<T>>,
    pub associated_types: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
    pub extensions: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
    pub child_types: FxHashMap<Symbol, FxHashMap<String, Symbol>>,
    pub initializers: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
    pub properties: FxHashMap<Symbol, IndexMap<Label, Symbol>>,
    pub instance_methods: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
    pub static_methods: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
    pub variants: FxHashMap<Symbol, IndexMap<Label, Symbol>>,
    pub method_requirements: FxHashMap<Symbol, IndexMap<Label, Symbol>>,
    pub instantiations: TrackedInstantiations<T>,
    pub member_witnesses: FxHashMap<NodeID, MemberWitness<T>>,
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
            member_witnesses: Default::default(),
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
            member_witnesses: self
                .member_witnesses
                .into_iter()
                .map(|(k, v)| {
                    (
                        k,
                        match v {
                            MemberWitness::Concrete(sym) => MemberWitness::Concrete(sym),
                            MemberWitness::Requirement(sym, ty) => MemberWitness::Requirement(
                                sym,
                                session.finalize_ty(ty).as_mono_ty().clone(),
                            ),
                            MemberWitness::Meta { receiver, label } => MemberWitness::Meta {
                                receiver: session.finalize_ty(receiver).as_mono_ty().clone(),
                                label,
                            },
                            MemberWitness::DefaultMethod {
                                method,
                                conformance,
                            } => MemberWitness::DefaultMethod {
                                method,
                                conformance,
                            },
                        },
                    )
                })
                .collect(),
            instantiations,
        }
    }
}

impl<T: SomeType> TypeCatalog<T> {
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
