use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    name::Name,
    node_id::NodeID,
    node_kinds::{
        attribute::Attribute, block::Block, generic_decl::GenericDecl, parameter::Parameter,
        type_annotation::TypeAnnotation,
    },
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectSet {
    pub names: Vec<Name>,
    pub is_open: bool,
}

impl Default for EffectSet {
    fn default() -> Self {
        Self {
            names: Default::default(),
            is_open: true,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Func {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    #[drive(skip)]
    pub name_span: Span,
    #[drive(skip)]
    pub effects: EffectSet,
    pub generics: Vec<GenericDecl>,
    pub params: Vec<Parameter>, /* params tuple */
    pub body: Block,
    pub ret: Option<TypeAnnotation>, /* return type */
    pub attributes: Vec<Attribute>,
}

impl_into_node!(Func);
