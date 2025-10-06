use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name::Name,
    name_resolution::symbol::{ProtocolId, Symbol, TypeId},
    node_id::NodeID,
    span::Span,
    types::{
        fields::Associated,
        passes::dependencies_pass::{Conformance, ConformanceRequirement},
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

fn import_label_symbol_map<
    I: IntoIterator<Item = (Label, Symbol)> + FromIterator<(Label, Symbol)>,
>(
    module_id: ModuleId,
    map: I,
) -> I {
    map.into_iter()
        .map(|(label, sym)| (label, sym.import(module_id)))
        .collect()
}

impl NominalForm {
    pub fn import(self, module_id: ModuleId) -> NominalForm {
        match self {
            NominalForm::Enum {
                variants,
                instance_methods,
                static_methods,
            } => NominalForm::Enum {
                variants: import_label_symbol_map(module_id, variants),
                instance_methods: import_label_symbol_map(module_id, instance_methods),
                static_methods: import_label_symbol_map(module_id, static_methods),
            },
            NominalForm::Struct {
                initializers,
                properties,
                instance_methods,
                static_methods,
            } => NominalForm::Struct {
                initializers: import_label_symbol_map(module_id, initializers),
                properties: import_label_symbol_map(module_id, properties),
                instance_methods: import_label_symbol_map(module_id, instance_methods),
                static_methods: import_label_symbol_map(module_id, static_methods),
            },
        }
    }

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

impl ConformanceStub {
    pub fn import(self, module_id: ModuleId) -> ConformanceStub {
        ConformanceStub {
            protocol_id: self.protocol_id.import(module_id),
            conforming_id: self.conforming_id.import(module_id),
            span: self.span,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Extension {
    pub node_id: NodeID,
    pub conformances: Vec<ConformanceStub>,
}

impl Extension {
    pub fn import(self, module_id: ModuleId) -> Extension {
        Extension {
            node_id: self.node_id,
            conformances: self
                .conformances
                .into_iter()
                .map(|c| ConformanceStub {
                    protocol_id: c.protocol_id.import(module_id),
                    conforming_id: c.conforming_id.import(module_id),
                    span: c.span,
                })
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Protocol {
    pub node_id: NodeID,
    pub methods: FxHashMap<Label, Symbol>,
    pub static_methods: FxHashMap<Label, Symbol>,
    pub associated_types: FxHashMap<Name, Associated>,
    pub requirements: FxHashMap<Label, ConformanceRequirement>,
}

impl Protocol {
    pub fn import(self, module_id: ModuleId) -> Protocol {
        Protocol {
            node_id: self.node_id,
            methods: import_label_symbol_map(module_id, self.methods),
            static_methods: import_label_symbol_map(module_id, self.static_methods),
            associated_types: self
                .associated_types
                .into_iter()
                .map(|(name, associated)| (name, associated.import(module_id)))
                .collect(),
            requirements: self
                .requirements
                .into_iter()
                .map(|(label, req)| (label, req.import(module_id)))
                .collect(),
        }
    }
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

impl Nominal {
    pub fn import(self, module_id: ModuleId) -> Nominal {
        Nominal {
            type_id: self.type_id.import(module_id),
            form: self.form.import(module_id),
            node_id: self.node_id,
            extensions: self
                .extensions
                .into_iter()
                .map(|e| e.import(module_id))
                .collect(),
            conformances: self
                .conformances
                .into_iter()
                .map(|e| e.import(module_id))
                .collect(),
            child_types: self
                .child_types
                .into_iter()
                .map(|(label, sym)| (label, sym.import(module_id)))
                .collect(),
        }
    }
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
