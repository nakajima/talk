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
    #[drive(skip)]
    pub name_span: Span,
    pub generics: Vec<GenericDecl>,
    pub conformances: Vec<TypeAnnotation>,
    pub default: Option<crate::node_kinds::generic_arg::GenericArg>,
    /// `Some` marks an ADR 0035 static value parameter (`static N: Int`);
    /// the annotation is the declared value type.
    pub static_ty: Option<TypeAnnotation>,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(GenericDecl);
