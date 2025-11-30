use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    span::Span,
    types::{
        infer_row::RowParamId,
        infer_ty::{InferTy, TypeParamId},
        ty::{SomeType, Ty},
        type_session::{MemberSource, TypeEntry, TypeSession},
    },
};

#[derive(Debug, Clone, PartialEq)]
pub struct Conformance<T> {
    pub node_id: NodeID,
    pub conforming_id: Symbol,
    pub protocol_id: ProtocolId,
    pub witnesses: FxHashMap<Label, Symbol>,
    pub associated_types: FxHashMap<Label, T>,
    pub span: Span,
}

impl Conformance<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> Conformance<Ty> {
        Conformance {
            node_id: self.node_id,
            conforming_id: self.conforming_id,
            protocol_id: self.protocol_id,
            witnesses: self.witnesses,
            associated_types: self
                .associated_types
                .into_iter()
                .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                .collect(),
            span: self.span,
        }
    }
}

impl From<Conformance<Ty>> for Conformance<InferTy> {
    fn from(value: Conformance<Ty>) -> Self {
        Conformance {
            node_id: value.node_id,
            conforming_id: value.conforming_id,
            protocol_id: value.protocol_id,
            witnesses: value.witnesses,
            associated_types: value
                .associated_types
                .into_iter()
                .map(|(k, v)| (k, v.into()))
                .collect(),
            span: value.span,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConformanceKey {
    pub protocol_id: ProtocolId,
    pub conforming_id: Symbol,
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
}
