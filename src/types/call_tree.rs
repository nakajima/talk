use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId, label::Label, name_resolution::symbol::Symbol, node_id::NodeID,
    types::infer_ty::Ty,
};

/// Information about a callee within a function, used for specialization propagation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CalleeInfo {
    /// Direct function call with known symbol
    Direct {
        sym: Symbol,
        /// The callee expression ID (uniquely identifies the call site)
        call_id: NodeID,
    },
    /// Method call whose resolved target/receiver shape is stored in ResolvedCalls.
    Member {
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
            CalleeInfo::Member { label, call_id } => CalleeInfo::Member { label, call_id },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CallReceiverKind {
    /// The semantic receiver is the receiver expression in `receiver.method(...)`.
    CalleeReceiver,
    /// The semantic receiver is one of the explicit call arguments, as in `Protocol.method(value)`.
    Argument { index: usize },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct CallReceiver {
    pub kind: CallReceiverKind,
    pub id: NodeID,
    /// The receiver type used for specialization. For variable receivers this is the
    /// lexical binding type, not necessarily the expression node's instantiated type.
    pub ty: Ty,
    pub symbol: Option<Symbol>,
}

impl CallReceiver {
    pub fn import(self, module_id: ModuleId) -> Self {
        Self {
            kind: self.kind,
            id: self.id,
            ty: self.ty.import(module_id),
            symbol: self.symbol.map(|symbol| symbol.import(module_id)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CallArgumentPlan {
    AsWritten,
    PrependReceiver { id: NodeID },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CallTarget {
    Direct { sym: Symbol },
    Constructor { constructor: Symbol },
    Member { member: Symbol, label: Label },
}

impl CallTarget {
    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            CallTarget::Direct { sym } => CallTarget::Direct {
                sym: sym.import(module_id),
            },
            CallTarget::Constructor { constructor } => CallTarget::Constructor {
                constructor: constructor.import(module_id),
            },
            CallTarget::Member { member, label } => CallTarget::Member {
                member: member.import(module_id),
                label,
            },
        }
    }

    pub fn symbol(&self) -> Symbol {
        match self {
            CallTarget::Direct { sym } => *sym,
            CallTarget::Constructor { constructor } => *constructor,
            CallTarget::Member { member, .. } => *member,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct CallShape {
    pub receiver: Option<CallReceiver>,
    pub argument_plan: CallArgumentPlan,
}

impl CallShape {
    pub fn as_written(receiver: Option<CallReceiver>) -> Self {
        Self {
            receiver,
            argument_plan: CallArgumentPlan::AsWritten,
        }
    }

    pub fn prepend_receiver(receiver: CallReceiver, id: NodeID) -> Self {
        Self {
            receiver: Some(receiver),
            argument_plan: CallArgumentPlan::PrependReceiver { id },
        }
    }

    fn same_receiver_source(&self, other: &Self) -> bool {
        self.argument_plan == other.argument_plan
            && match (&self.receiver, &other.receiver) {
                (None, None) => true,
                (Some(lhs), Some(rhs)) => {
                    lhs.kind == rhs.kind && lhs.id == rhs.id && lhs.symbol == rhs.symbol
                }
                _ => false,
            }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ResolvedCall {
    pub target: CallTarget,
    pub receiver: Option<CallReceiver>,
    pub argument_plan: CallArgumentPlan,
}

impl ResolvedCall {
    pub fn new(target: CallTarget, shape: CallShape) -> Self {
        Self {
            target,
            receiver: shape.receiver,
            argument_plan: shape.argument_plan,
        }
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        Self {
            target: self.target.import(module_id),
            receiver: self.receiver.map(|receiver| receiver.import(module_id)),
            argument_plan: self.argument_plan,
        }
    }

    pub fn symbol(&self) -> Symbol {
        self.target.symbol()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct PendingResolvedCall {
    pub shape: Option<CallShape>,
    pub target_candidates: Vec<CallTarget>,
}

impl PendingResolvedCall {
    pub fn record_shape(&mut self, shape: CallShape) {
        if let Some(existing) = &self.shape {
            assert!(
                existing.same_receiver_source(&shape),
                "conflicting call shapes recorded for one callee expression: {existing:?} vs {shape:?}"
            );
        }
        self.shape = Some(shape);
    }

    pub fn record_target(&mut self, target: CallTarget) {
        if self.target_candidates.contains(&target) {
            return;
        }
        self.target_candidates.push(target);
    }
}

/// Maps each function to the list of callees in its body.
pub type CallTree = FxHashMap<Symbol, Vec<CalleeInfo>>;

/// Solver-time pending call facts keyed by callee expression ID.
pub type PendingResolvedCalls = FxHashMap<NodeID, PendingResolvedCall>;

/// Maps call callee expression IDs to type-checker-resolved call facts.
pub type ResolvedCalls = FxHashMap<NodeID, ResolvedCall>;
