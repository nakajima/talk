use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    span::Span,
    types::infer_ty::Ty,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConformanceKey {
    pub protocol_id: ProtocolId,
    pub conforming_id: Symbol,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Witnesses {
    pub methods: FxHashMap<Label, Symbol>,
    pub associated_types: FxHashMap<Label, Ty>,
    pub requirements: FxHashMap<Symbol, Symbol>,
}

impl Witnesses {
    /// Look up a witness by label, falling back to lookup by method requirement symbol.
    pub fn get_witness(&self, label: &Label, method_req: &Symbol) -> Option<Symbol> {
        self.methods
            .get(label)
            .copied()
            .or_else(|| self.requirements.get(method_req).copied())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Conformance {
    pub node_id: NodeID,
    pub conforming_id: Symbol,
    pub protocol_id: ProtocolId,
    pub witnesses: Witnesses,
    pub span: Span,
}
