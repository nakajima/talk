use rustc_hash::FxHashMap;

use crate::{label::Label, name_resolution::symbol::Symbol, node_id::NodeID};

/// Information about a callee within a function, used for specialization propagation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CalleeInfo {
    /// Direct function call with known symbol
    Direct { sym: Symbol, call_id: NodeID },
    /// Method call on a receiver
    Member {
        receiver_id: NodeID,
        label: Label,
        call_id: NodeID,
    },
}

/// Maps each function to the list of callees in its body.
pub type CallTree = FxHashMap<Symbol, Vec<CalleeInfo>>;
