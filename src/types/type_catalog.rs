use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::{ProtocolId, Symbol, TypeId},
    node_id::NodeID,
    span::Span,
    types::{
        fields::Associated,
        passes::dependencies_pass::{Conformance, ConformanceRequirement},
        scheme::Scheme,
    },
};

#[derive(Debug, PartialEq, Clone)]
pub enum NominalForm {
    Struct {
        initializers: FxHashMap<Label, Symbol>,
        properties: IndexMap<Label, Symbol>,
        instance_methods: FxHashMap<Label, Symbol>,
        static_methods: FxHashMap<Label, Symbol>,
    },
    Enum {
        variants: FxHashMap<Label, Symbol>,
        instance_methods: FxHashMap<Label, Symbol>,
        static_methods: FxHashMap<Label, Symbol>,
    },
}

impl NominalForm {
    pub fn extend_methods(&mut self, methods: FxHashMap<Label, Symbol>) {
        let (Self::Struct {
            instance_methods, ..
        }
        | Self::Enum {
            instance_methods, ..
        }) = self;

        instance_methods.extend(methods);
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct ConformanceStub {
    pub protocol_id: ProtocolId,
    pub conforming_id: Symbol,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Extension {
    pub node_id: NodeID,
    pub conformances: Vec<ConformanceStub>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Protocol {
    pub node_id: NodeID,
    pub methods: FxHashMap<Label, Symbol>,
    pub associated_types: FxHashMap<Name, Associated>,
    pub static_methods: FxHashMap<Label, Symbol>,
    pub requirements: FxHashMap<Label, ConformanceRequirement>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Nominal {
    pub type_id: TypeId,
    pub form: NominalForm,
    pub node_id: NodeID,
    pub extensions: Vec<Extension>,
    pub conformances: Vec<ConformanceStub>,
    pub child_types: FxHashMap<String, Symbol>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConformanceKey {
    pub protocol_id: ProtocolId,
    pub conforming_id: Symbol,
}

#[derive(Debug, PartialEq, Default, Clone)]
pub struct TypeCatalog {
    pub nominals: FxHashMap<Symbol, Nominal>,
    pub protocols: FxHashMap<ProtocolId, Protocol>,
    pub conformances: FxHashMap<ConformanceKey, Conformance>,
    pub aliases: FxHashMap<Symbol, Scheme>,
}

impl Nominal {
    pub fn member_symbol(&self, label: &Label) -> Option<&Symbol> {
        match &self.form {
            NominalForm::Enum {
                variants,
                instance_methods: methods,
                static_methods,
            } => {
                if let Some(sym) = variants.get(label) {
                    return Some(sym);
                }

                if let Some(sym) = methods.get(label) {
                    return Some(sym);
                }

                if let Some(sym) = static_methods.get(label) {
                    return Some(sym);
                }

                None
            }
            NominalForm::Struct {
                instance_methods: methods,
                properties,
                static_methods,
                ..
            } => {
                if let Some(sym) = methods.get(label) {
                    return Some(sym);
                }

                if let Some(sym) = properties.get(label) {
                    return Some(sym);
                }

                if let Some(sym) = static_methods.get(label) {
                    return Some(sym);
                }

                None
            }
        }
    }
}
