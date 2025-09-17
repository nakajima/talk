use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::symbol::{Symbol, TypeId},
    node_id::NodeID,
    span::Span,
    types::row::Row,
};

#[derive(Debug, PartialEq)]
pub enum NominalForm {
    Struct {
        initializers: FxHashMap<Label, Symbol>,
        properties: Box<Row>,
        methods: FxHashMap<Label, Symbol>,
        static_methods: FxHashMap<Label, Symbol>,
    },
    Enum {
        variants: Box<Row>,
        methods: FxHashMap<Label, Symbol>,
        static_methods: FxHashMap<Label, Symbol>,
    },
}

#[derive(Debug, PartialEq)]
pub struct Extension {
    pub node_id: NodeID,
    pub methods: FxHashMap<Label, Symbol>,
    pub conformances: Vec<TypeId>,
}

#[derive(Debug, PartialEq)]
pub struct Protocol {
    pub node_id: NodeID,
    pub methods: FxHashMap<Label, Symbol>,
}

#[derive(Debug, PartialEq)]
pub struct Nominal {
    pub form: NominalForm,
    pub node_id: NodeID,
    pub extensions: Vec<Extension>,
}

#[derive(Debug, PartialEq, Default)]
pub struct TypeCatalog {
    pub nominals: FxHashMap<TypeId, Nominal>,
    pub protocols: FxHashMap<TypeId, Protocol>,
}
