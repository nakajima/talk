use crate::{
    parsing::span::Span, impl_into_node, name::Name, node::Node, node_id::NodeID,
    node_kinds::type_annotation::TypeAnnotation,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub id: NodeID,
    pub name: Name,
    pub type_annotation: Option<TypeAnnotation>,
    pub span: Span,
}

impl_into_node!(Parameter);

impl Parameter {
    pub fn new(
        id: NodeID,
        name: Name,
        type_annotation: Option<TypeAnnotation>,
        span: Span,
    ) -> Self {
        Self {
            id,
            name,
            type_annotation,
            span,
        }
    }
}
