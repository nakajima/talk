use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::symbol::{Symbol, TypeId},
    node_id::NodeID,
};

#[derive(Debug, PartialEq, Clone)]
pub enum NominalForm {
    Struct {
        initializers: FxHashMap<Label, Symbol>,
        properties: IndexMap<Label, Symbol>,
        methods: FxHashMap<Label, Symbol>,
        static_methods: FxHashMap<Label, Symbol>,
    },
    Enum {
        variants: FxHashMap<Label, Symbol>,
        methods: FxHashMap<Label, Symbol>,
        static_methods: FxHashMap<Label, Symbol>,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub struct Extension {
    pub node_id: NodeID,
    pub methods: FxHashMap<Label, Symbol>,
    pub conformances: Vec<TypeId>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Protocol {
    pub node_id: NodeID,
    pub methods: FxHashMap<Label, Symbol>,
    pub method_requirements: FxHashMap<Label, Symbol>,
}

#[derive(Debug, PartialEq, Clone)]
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

impl Nominal {
    pub fn member_symbol(&self, label: &Label) -> Option<&Symbol> {
        match &self.form {
            NominalForm::Enum {
                variants,
                methods,
                static_methods: _,
            } => {
                if let Some(sym) = variants.get(label) {
                    return Some(sym);
                }

                if let Some(sym) = methods.get(label) {
                    return Some(sym);
                }

                None
            }
            NominalForm::Struct {
                methods,
                properties,
                static_methods: _,
                ..
            } => {
                if let Some(sym) = methods.get(label) {
                    return Some(sym);
                }

                if let Some(sym) = properties.get(label) {
                    return Some(sym);
                }

                None
            }
        }
    }
}
