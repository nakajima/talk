use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId, label::Label, name_resolution::symbol::Symbol, node_id::NodeID,
};

/// Information about a callee within a function, used for specialization propagation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CalleeInfo {
    /// Direct function call with known symbol
    Direct {
        sym: Symbol,
        /// The callee expression ID (uniquely identifies the call site)
        call_id: NodeID,
    },
    /// Method call on a receiver
    Member {
        receiver_id: NodeID,
        label: Label,
        /// The callee expression ID (uniquely identifies the call site)
        call_id: NodeID,
    },
}

impl CalleeInfo {
    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            CalleeInfo::Direct { sym, call_id } => CalleeInfo::Direct {
                sym: sym.import(module_id),
                call_id,
            },
            CalleeInfo::Member {
                receiver_id,
                label,
                call_id,
            } => CalleeInfo::Member {
                receiver_id,
                label,
                call_id,
            },
        }
    }
}

/// Maps each function to the list of callees in its body.
pub type CallTree = FxHashMap<Symbol, Vec<CalleeInfo>>;
