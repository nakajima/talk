use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    span::Span,
    types::{
        infer_ty::{Infer, InferTy, InnerTy, TypePhase},
        ty::{Ty, Typed},
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConformanceKey {
    pub protocol_id: ProtocolId,
    pub conforming_id: Symbol,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Witnesses<T: TypePhase> {
    pub methods: FxHashMap<Label, Symbol>,
    pub associated_types: FxHashMap<Label, InnerTy<T>>,
    pub requirements: FxHashMap<Symbol, Symbol>,
}

impl<T: TypePhase> Default for Witnesses<T> {
    fn default() -> Self {
        Self {
            methods: Default::default(),
            associated_types: Default::default(),
            requirements: Default::default(),
        }
    }
}

impl<T: TypePhase> Witnesses<T> {
    /// Look up a witness by label, falling back to lookup by method requirement symbol.
    pub fn get_witness(&self, label: &Label, method_req: &Symbol) -> Option<Symbol> {
        self.methods
            .get(label)
            .copied()
            .or_else(|| self.requirements.get(method_req).copied())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Conformance<T: TypePhase> {
    pub node_id: NodeID,
    pub conforming_id: Symbol,
    pub protocol_id: ProtocolId,
    pub witnesses: Witnesses<T>,
    pub span: Span,
}

impl Conformance<Infer> {
    pub(super) fn finalize(self, session: &mut TypeSession) -> Conformance<Typed> {
        Conformance {
            node_id: self.node_id,
            conforming_id: self.conforming_id,
            protocol_id: self.protocol_id,
            witnesses: Witnesses {
                methods: self.witnesses.methods,
                associated_types: self
                    .witnesses
                    .associated_types
                    .into_iter()
                    .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                    .collect(),
                requirements: self.witnesses.requirements,
            },
            span: self.span,
        }
    }
}
