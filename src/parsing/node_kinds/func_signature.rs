use derive_visitor::{Drive, DriveMut};

use crate::{
    name::Name,
    node_id::NodeID,
    node_kinds::{
        generic_decl::GenericDecl, parameter::Parameter, type_annotation::TypeAnnotation,
    },
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct FuncSignature {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub span: Span,
    #[drive(skip)]
    pub name: Name,
    pub params: Vec<Parameter>,
    pub generics: Vec<GenericDecl>,
    pub ret: Option<Box<TypeAnnotation>>,
}
