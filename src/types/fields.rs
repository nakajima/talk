use indexmap::IndexMap;

use crate::{label::Label, name::Name, name_resolution::symbol::Symbol};

#[derive(Debug, PartialEq, Clone)]
pub enum TypeFields<T> {
    Struct {
        initializers: IndexMap<Name, Initializer<T>>,
        methods: IndexMap<Label, Method<T>>,
        properties: IndexMap<Label, Property<T>>,
    },
    Protocol {
        initializers: IndexMap<Name, Initializer<T>>,
        methods: IndexMap<Label, Method<T>>,
        method_requirements: IndexMap<Name, MethodRequirement<T>>,
        properties: IndexMap<Label, Property<T>>,
        associated_types: IndexMap<Name, Associated>,
    },
    Enum {
        variants: IndexMap<Name, Variant<T>>,
        methods: IndexMap<Label, Method<T>>,
    },
    Primitive,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Property<T> {
    pub is_static: bool,
    pub ty_repr: T,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Method<T> {
    pub symbol: Symbol,
    pub is_static: bool,
    pub params: Vec<T>,
    pub ret: T,
}

#[derive(Debug, PartialEq, Clone)]
pub struct MethodRequirement<T> {
    pub params: Vec<T>,
    pub ret: T,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Initializer<T> {
    pub params: Vec<T>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Variant<T> {
    pub fields: Vec<T>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Associated {}
