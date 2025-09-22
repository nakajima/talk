use indexmap::IndexMap;

use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::{Symbol, TypeId},
    node_id::NodeID,
    span::Span,
};

#[derive(Debug, PartialEq, Clone)]
pub enum TypeFields<T> {
    Struct {
        initializers: IndexMap<Label, Initializer<T>>,
        instance_methods: IndexMap<Label, Method<T>>,
        static_methods: IndexMap<Label, Method<T>>,
        properties: IndexMap<Label, Property<T>>,
    },
    Extension {
        instance_methods: IndexMap<Label, Method<T>>,
        static_methods: IndexMap<Label, Method<T>>,
    },
    Protocol {
        instance_methods: IndexMap<Label, Method<T>>,
        method_requirements: IndexMap<Label, MethodRequirement<T>>,
        static_methods: IndexMap<Label, Method<T>>,
        associated_types: IndexMap<Name, Associated>,
    },
    Enum {
        variants: IndexMap<Label, Variant<T>>,
        instance_methods: IndexMap<Label, Method<T>>,
        static_methods: IndexMap<Label, Method<T>>,
    },
    Primitive,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Property<T> {
    pub symbol: Symbol,
    pub is_static: bool,
    pub ty_repr: T,
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub struct Method<T> {
    pub id: NodeID,
    pub span: Span,
    pub symbol: Symbol,
    pub is_static: bool,
    pub params: Vec<T>,
    pub ret: T,
}

#[derive(Debug, PartialEq, Clone)]
pub struct MethodRequirement<T> {
    pub id: NodeID,
    pub symbol: Symbol,
    pub params: Vec<T>,
    pub ret: T,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Initializer<T> {
    pub symbol: Symbol,
    pub initializes_type_id: TypeId,
    pub params: Vec<T>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Variant<T> {
    pub symbol: Symbol,
    pub tag: Label,
    pub fields: Vec<T>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Associated {}
