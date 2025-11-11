use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name::Name,
    name_resolution::symbol::{InstanceMethodId, MethodRequirementId, ProtocolId, Symbol},
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
pub enum ConformanceRequirement {
    UnfulfilledInstanceMethod(MethodRequirementId),
    FulfilledInstanceMethod(InstanceMethodId),
}

impl ConformanceRequirement {
    pub fn import(self, module_id: ModuleId) -> ConformanceRequirement {
        match self {
            ConformanceRequirement::UnfulfilledInstanceMethod(id) => {
                ConformanceRequirement::UnfulfilledInstanceMethod(id.import(module_id))
            }
            ConformanceRequirement::FulfilledInstanceMethod(id) => {
                ConformanceRequirement::FulfilledInstanceMethod(id.import(module_id))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Conformance {
    pub node_id: NodeID,
    pub conforming_id: Symbol,
    pub protocol_id: ProtocolId,
    pub requirements: FxHashMap<Label, ConformanceRequirement>,
    pub associated_types: FxHashMap<Label, InferTy>,
    pub span: Span,
}

fn import_label_symbol_map<
    I: IntoIterator<Item = (Label, Symbol)> + FromIterator<(Label, Symbol)>,
>(
    module_id: ModuleId,
    map: I,
) -> I {
    map.into_iter()
        .map(|(label, sym)| (label, sym.import(module_id)))
        .collect()
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct ConformanceStub {
    pub protocol_id: ProtocolId,
    pub conforming_id: Symbol,
    pub span: Span,
}

impl ConformanceStub {
    pub fn import(self, module_id: ModuleId) -> ConformanceStub {
        ConformanceStub {
            protocol_id: self.protocol_id.import(module_id),
            conforming_id: self.conforming_id.import(module_id),
            span: self.span,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Extension {
    pub node_id: NodeID,
    pub conformances: Vec<ConformanceStub>,
}

impl Extension {
    pub fn import(self, module_id: ModuleId) -> Extension {
        Extension {
            node_id: self.node_id,
            conformances: self
                .conformances
                .into_iter()
                .map(|c| ConformanceStub {
                    protocol_id: c.protocol_id.import(module_id),
                    conforming_id: c.conforming_id.import(module_id),
                    span: c.span,
                })
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct ProtocolOld {
    pub node_id: NodeID,
    pub static_methods: FxHashMap<Label, Symbol>,
    pub associated_types: IndexMap<Name, Symbol>,
    pub requirements: FxHashMap<Label, ConformanceRequirement>,
}

impl ProtocolOld {
    pub fn import(self, module_id: ModuleId) -> ProtocolOld {
        ProtocolOld {
            node_id: self.node_id,
            static_methods: import_label_symbol_map(module_id, self.static_methods),
            associated_types: self
                .associated_types
                .into_iter()
                .map(|(name, associated)| (name, associated.import(module_id)))
                .collect(),
            requirements: self
                .requirements
                .into_iter()
                .map(|(label, req)| (label, req.import(module_id)))
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct NominalOld {
    pub symbol: Symbol,
    pub node_id: NodeID,
}

impl NominalOld {
    pub fn import(self, module_id: ModuleId) -> NominalOld {
        NominalOld {
            symbol: self.symbol.import(module_id),
            node_id: self.node_id,
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
pub struct TypeCatalogOld<T: SomeType> {
    pub conformances: FxHashMap<ConformanceKey, Conformance>,
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
}

impl<T: SomeType> Default for TypeCatalogOld<T> {
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
        }
    }
}

impl TypeCatalogOld<InferTy> {
    pub fn finalize(self, session: &mut TypeSession) -> TypeCatalogOld<Ty> {
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
        TypeCatalogOld {
            associated_types: self.associated_types,
            conformances: self.conformances,
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

impl<T: SomeType> TypeCatalogOld<T> {
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
