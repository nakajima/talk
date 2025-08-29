use derive_visitor::{Drive, DriveMut};

use crate::{
    name::Name,
    node_id::NodeID,
    node_kinds::{
        attribute::Attribute, block::Block, generic_decl::GenericDecl, parameter::Parameter,
        type_annotation::TypeAnnotation,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Func {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    pub generics: Vec<GenericDecl>,
    pub params: Vec<Parameter>, /* params tuple */
    pub body: Block,
    pub ret: Option<TypeAnnotation>, /* return type */
    pub attributes: Vec<Attribute>,
}
