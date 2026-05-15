use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    span::Span,
    types::infer_ty::Ty,
};

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct ConformanceKey {
    pub protocol_id: ProtocolId,
    pub conforming_id: Symbol,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ConformanceClaim {
    pub node_id: NodeID,
    pub conforming_id: Symbol,
    pub protocol_id: ProtocolId,
    pub span: Span,
    pub associated_type_candidates: IndexMap<Label, Symbol>,
    pub method_candidates: IndexMap<Label, Symbol>,
}

impl ConformanceClaim {
    pub fn new(
        node_id: NodeID,
        conforming_id: Symbol,
        protocol_id: ProtocolId,
        span: Span,
    ) -> Self {
        Self {
            node_id,
            conforming_id,
            protocol_id,
            span,
            associated_type_candidates: Default::default(),
            method_candidates: Default::default(),
        }
    }

    pub fn key(&self) -> ConformanceKey {
        ConformanceKey {
            protocol_id: self.protocol_id,
            conforming_id: self.conforming_id,
        }
    }

    pub fn merge_candidates(&mut self, other: ConformanceClaim) {
        self.associated_type_candidates
            .extend(other.associated_type_candidates);
        self.method_candidates.extend(other.method_candidates);
    }

    pub fn import_as(self, module_id: ModuleId) -> Self {
        Self {
            node_id: self.node_id,
            conforming_id: self.conforming_id.import(module_id),
            protocol_id: self.protocol_id.import(module_id),
            span: self.span,
            associated_type_candidates: self
                .associated_type_candidates
                .into_iter()
                .map(|(label, sym)| (label, sym.import(module_id)))
                .collect(),
            method_candidates: self
                .method_candidates
                .into_iter()
                .map(|(label, sym)| (label, sym.import(module_id)))
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Default, serde::Serialize, serde::Deserialize)]
pub struct WitnessTable {
    pub methods: FxHashMap<Label, Symbol>,
    pub associated_types: FxHashMap<Label, Ty>,
    pub requirements: FxHashMap<Symbol, Symbol>,
}

impl WitnessTable {
    /// Look up a witness by label, falling back to lookup by method requirement symbol.
    pub fn get_witness(&self, label: &Label, method_req: &Symbol) -> Option<Symbol> {
        self.methods
            .get(label)
            .copied()
            .or_else(|| self.requirements.get(method_req).copied())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ConformanceOrigin {
    Declared,
    AutoDerived,
    Inherited,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ConformanceEvidence {
    pub node_id: NodeID,
    pub conforming_id: Symbol,
    pub protocol_id: ProtocolId,
    pub origin: ConformanceOrigin,
    pub witnesses: WitnessTable,
    pub span: Span,
}

impl ConformanceEvidence {
    pub fn declared(
        node_id: NodeID,
        conforming_id: Symbol,
        protocol_id: ProtocolId,
        span: Span,
    ) -> Self {
        Self {
            node_id,
            conforming_id,
            protocol_id,
            origin: ConformanceOrigin::Declared,
            witnesses: WitnessTable::default(),
            span,
        }
    }

    pub fn from_claim(claim: &ConformanceClaim) -> Self {
        Self {
            node_id: claim.node_id,
            conforming_id: claim.conforming_id,
            protocol_id: claim.protocol_id,
            origin: ConformanceOrigin::Declared,
            witnesses: WitnessTable::default(),
            span: claim.span,
        }
    }

    pub(crate) fn from_superprotocol(
        node_id: NodeID,
        conforming_id: Symbol,
        protocol_id: ProtocolId,
        span: Span,
    ) -> Self {
        Self {
            node_id,
            conforming_id,
            protocol_id,
            origin: ConformanceOrigin::Inherited,
            witnesses: WitnessTable::default(),
            span,
        }
    }

    pub fn auto_derived(
        conforming_id: Symbol,
        protocol_id: ProtocolId,
        witnesses: WitnessTable,
    ) -> Self {
        Self {
            node_id: NodeID::SYNTHESIZED,
            conforming_id,
            protocol_id,
            origin: ConformanceOrigin::AutoDerived,
            witnesses,
            span: Span::SYNTHESIZED,
        }
    }
}
