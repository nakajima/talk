use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    span::Span,
    types::{infer_ty::InferTy, ty::Ty, type_session::TypeSession},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConformanceKey {
    pub protocol_id: ProtocolId,
    pub conforming_id: Symbol,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Witnesses<T> {
    pub methods: FxHashMap<Label, Symbol>,
    pub associated_types: FxHashMap<Label, T>,
}

impl<T> Default for Witnesses<T> {
    fn default() -> Self {
        Self {
            methods: Default::default(),
            associated_types: Default::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Conformance<T> {
    pub node_id: NodeID,
    pub conforming_id: Symbol,
    pub protocol_id: ProtocolId,
    pub witnesses: Witnesses<T>,
    pub span: Span,
}

impl Conformance<InferTy> {
    pub(super) fn finalize(self, session: &mut TypeSession) -> Conformance<Ty> {
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
            },
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
            witnesses: Witnesses {
                methods: value.witnesses.methods,
                associated_types: value
                    .witnesses
                    .associated_types
                    .into_iter()
                    .map(|(k, v)| (k, v.into()))
                    .collect(),
            },
            span: value.span,
        }
    }
}
