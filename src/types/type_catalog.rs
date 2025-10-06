use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name::Name,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    span::Span,
    types::{
        fields::Associated,
        passes::dependencies_pass::{Conformance, ConformanceRequirement},
    },
};

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
    pub associated_types: IndexMap<Name, Associated>,
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
    pub symbol: Symbol,
    pub node_id: NodeID,
}

impl Nominal {
    pub fn import(self, module_id: ModuleId) -> Nominal {
        Nominal {
            symbol: self.symbol.import(module_id),
            node_id: self.node_id,
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
    pub extensions: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
    pub child_types: FxHashMap<Symbol, FxHashMap<String, Symbol>>,

    pub initializers: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
    pub properties: FxHashMap<Symbol, IndexMap<Label, Symbol>>,
    pub instance_methods: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
    pub static_methods: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
    pub variants: FxHashMap<Symbol, FxHashMap<Label, Symbol>>,
}
