use rustc_hash::FxHashMap;

use crate::{
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

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Conformance {
    pub node_id: NodeID,
    pub conforming_id: Symbol,
    pub protocol_id: ProtocolId,
    pub witnesses: WitnessTable,
    pub span: Span,
}

impl Conformance {
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
            witnesses: WitnessTable::default(),
            span,
        }
    }

    pub fn inherited(
        node_id: NodeID,
        conforming_id: Symbol,
        protocol_id: ProtocolId,
        span: Span,
    ) -> Self {
        Self {
            node_id,
            conforming_id,
            protocol_id,
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
            witnesses,
            span: Span::SYNTHESIZED,
        }
    }
}
