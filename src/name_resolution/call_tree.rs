use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use crate::{label::Label, name_resolution::symbol::Symbol, node_id::NodeID};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawCallee {
    Symbol(Symbol),
    Member { receiver_id: NodeID, label: Label },
    Unqualified { node_id: NodeID, label: Label },
}

impl std::hash::Hash for RawCallee {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::Symbol(sym) => sym.hash(state),
            Self::Member { receiver_id, label } => {
                receiver_id.hash(state);
                label.hash(state);
            }
            Self::Unqualified { node_id, label } => {
                node_id.hash(state);
                label.hash(state);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct CallTree<T: Eq + std::hash::Hash> {
    calls: FxHashMap<Symbol, IndexSet<T>>,
}

impl<T: std::hash::Hash + Eq> Default for CallTree<T> {
    fn default() -> Self {
        Self {
            calls: Default::default(),
        }
    }
}

impl<T: std::hash::Hash + Eq> CallTree<T> {
    pub fn track(&mut self, caller: Symbol, callee: T) {
        self.calls.entry(caller).or_default().insert(callee);
    }

    pub fn lookup(&self, caller: &Symbol) -> Option<&IndexSet<T>> {
        self.calls.get(caller)
    }
}
