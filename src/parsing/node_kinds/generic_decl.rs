use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, name::Name, node_id::NodeID, node_kinds::type_annotation::TypeAnnotation,
    parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct GenericDecl {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    pub generics: Vec<GenericDecl>,
    pub conformances: Vec<TypeAnnotation>,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(GenericDecl);
