use indexmap::{IndexMap, IndexSet};

use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    span::Span,
    types::{
        infer_ty::TypeParamId, members::Members, scheme::ForAll, type_catalog::ConformanceStub,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub struct AssociatedType {
    pub symbol: Symbol,
    pub type_param_id: TypeParamId,
    pub conformances: Vec<(ProtocolId, Span)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Protocol<T> {
    pub name: Name,
    pub node_id: NodeID,
    pub self_id: TypeParamId,
    pub associated_types: IndexMap<Label, AssociatedType>,
    pub method_requirements: IndexMap<Label, T>,
    pub conformances: Vec<ConformanceStub>,
    pub child_types: IndexMap<Label, Symbol>,
    pub members: Members<T>,
}

impl<T> Protocol<T> {
    pub fn collect_foralls(&self) -> IndexSet<ForAll> {
        let mut foralls = IndexSet::default();

        foralls.insert(ForAll::Ty(self.self_id));
        foralls.extend(
            self.associated_types
                .values()
                .map(|associated| ForAll::Ty(associated.type_param_id)),
        );

        foralls
    }
}
