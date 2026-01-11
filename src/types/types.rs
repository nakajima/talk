use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{matcher::MatchPlan, ty::Ty, type_catalog::TypeCatalog, type_session::TypeEntry},
};

// the Types object is the final result of the type checking phase
#[derive(Clone, Debug, Default)]
pub struct Types {
    pub types_by_node: FxHashMap<NodeID, TypeEntry>,
    pub types_by_symbol: FxHashMap<Symbol, TypeEntry>,
    pub catalog: TypeCatalog<Ty>,
    pub(crate) match_plans: FxHashMap<NodeID, MatchPlan>,
}

impl Types {
    pub fn define(&mut self, symbol: Symbol, ty: TypeEntry) {
        self.types_by_symbol.insert(symbol, ty);
    }

    pub fn get(&self, id: &NodeID) -> Option<&TypeEntry> {
        self.types_by_node.get(id)
    }

    pub fn get_symbol(&self, sym: &Symbol) -> Option<&TypeEntry> {
        self.types_by_symbol.get(sym)
    }

    pub fn import_as(self, module_id: ModuleId) -> Types {
        Types {
            types_by_node: self
                .types_by_node
                .into_iter()
                .map(|(k, v)| (k, v.import(module_id)))
                .collect(),
            types_by_symbol: self
                .types_by_symbol
                .into_iter()
                .map(|(k, v)| (k.import(module_id), v.import(module_id)))
                .collect(),
            catalog: self.catalog.import_as(module_id),
            match_plans: self.match_plans,
        }
    }
}
