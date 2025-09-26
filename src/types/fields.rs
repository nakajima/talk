use indexmap::IndexMap;

use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::{Symbol, TypeId},
    node_id::NodeID,
    span::Span,
    types::type_session::ASTTyRepr,
};

#[derive(Debug, PartialEq, Clone)]
pub enum TypeFields {
    Struct {
        initializers: IndexMap<Label, Initializer>,
        instance_methods: IndexMap<Label, Method>,
        static_methods: IndexMap<Label, Method>,
        properties: IndexMap<Label, Property>,
    },
    Extension {
        instance_methods: IndexMap<Label, Method>,
        static_methods: IndexMap<Label, Method>,
    },
    Protocol {
        instance_methods: IndexMap<Label, Method>,
        method_requirements: IndexMap<Label, MethodRequirement>,
        static_methods: IndexMap<Label, Method>,
        associated_types: IndexMap<Name, Associated>,
    },
    Enum {
        variants: IndexMap<Label, Variant>,
        instance_methods: IndexMap<Label, Method>,
        static_methods: IndexMap<Label, Method>,
    },
    Primitive,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Property {
    pub symbol: Symbol,
    pub is_static: bool,
    pub ty_repr: ASTTyRepr,
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub struct Method {
    pub id: NodeID,
    pub span: Span,
    pub symbol: Symbol,
    pub is_static: bool,
    pub params: Vec<ASTTyRepr>,
    pub ret: ASTTyRepr,
}

#[derive(Debug, PartialEq, Clone)]
pub struct MethodRequirement {
    pub id: NodeID,
    pub symbol: Symbol,
    pub params: Vec<ASTTyRepr>,
    pub ret: ASTTyRepr,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Initializer {
    pub symbol: Symbol,
    pub initializes_type_id: TypeId,
    pub params: Vec<ASTTyRepr>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Variant {
    pub symbol: Symbol,
    pub tag: Label,
    pub fields: Vec<ASTTyRepr>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Associated {}
