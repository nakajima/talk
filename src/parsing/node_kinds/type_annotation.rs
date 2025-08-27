use crate::{impl_into_node, name::Name, node::Node, node_id::NodeID, parsing::span::Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeAnnotationKind {
    Func {
        params: Vec<TypeAnnotation>,
        returns: Box<TypeAnnotation>,
    },
    Nominal {
        name: Name,
        generics: Vec<TypeAnnotation>,
    },
    Tuple(Vec<TypeAnnotation>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeAnnotation {
    pub id: NodeID,
    pub kind: TypeAnnotationKind,
    pub span: Span,
}

impl_into_node!(TypeAnnotation);
