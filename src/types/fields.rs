use indexmap::IndexMap;

use crate::{name::Name, types::type_session::TypingPhase};

#[derive(Debug, PartialEq, Clone)]
pub enum TypeFields<P: TypingPhase> {
    Struct {
        initializers: IndexMap<Name, Initializer<P>>,
        methods: IndexMap<Name, Method<P>>,
        properties: IndexMap<Name, Property<P>>,
    },
    Protocol {
        initializers: IndexMap<Name, Initializer<P>>,
        methods: IndexMap<Name, Method<P>>,
        method_requirements: IndexMap<Name, MethodRequirement<P>>,
        properties: IndexMap<Name, Property<P>>,
        associated_types: IndexMap<Name, Associated>,
    },
    Enum {
        variants: IndexMap<Name, Variant<P>>,
        methods: IndexMap<Name, Method<P>>,
    },
    Primitive,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Property<P: TypingPhase> {
    pub is_static: bool,
    pub ty_repr: P::TyPhase,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Method<P: TypingPhase> {
    pub is_static: bool,
    pub params: Vec<P::TyPhase>,
    pub ret: P::TyPhase,
}

#[derive(Debug, PartialEq, Clone)]
pub struct MethodRequirement<P: TypingPhase> {
    pub params: Vec<P::TyPhase>,
    pub ret: P::TyPhase,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Initializer<P: TypingPhase> {
    pub params: Vec<P::TyPhase>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Variant<P: TypingPhase> {
    pub fields: Vec<P::TyPhase>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Associated {}
