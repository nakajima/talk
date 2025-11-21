use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, name::Name, node_id::NodeID, node_kinds::type_annotation::TypeAnnotation,
    parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Parameter {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    #[drive(skip)]
    pub name_span: Span,
    pub type_annotation: Option<TypeAnnotation>,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(Parameter);

impl Parameter {
    pub fn new(
        id: NodeID,
        name: Name,
        name_span: Span,
        type_annotation: Option<TypeAnnotation>,
        span: Span,
    ) -> Self {
        Self {
            id,
            name,
            name_span,
            type_annotation,
            span,
        }
    }
}
