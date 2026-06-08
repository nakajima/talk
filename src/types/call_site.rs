use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        call_substitutions::CallSubstitutions,
        conformance::ConformanceKey,
        infer_ty::Ty,
        typed_ast::{TypedExpr, TypedExprKind},
    },
};

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct CallSiteId(NodeID);

impl CallSiteId {
    pub fn from_call(expr: &TypedExpr) -> Self {
        let TypedExprKind::Call { callee, .. } = &expr.kind else {
            panic!(
                "CallSiteId::from_call called for non-call expression: {:?}",
                expr.kind
            );
        };
        Self(callee.id)
    }

    pub fn from_effect(expr: &TypedExpr) -> Self {
        let TypedExprKind::CallEffect { .. } = &expr.kind else {
            panic!(
                "CallSiteId::from_effect called for non-effect-call expression: {:?}",
                expr.kind
            );
        };
        Self(expr.id)
    }

    pub fn from_constructor(expr: &TypedExpr) -> Self {
        match &expr.kind {
            TypedExprKind::Call { callee, .. }
                if matches!(callee.kind, TypedExprKind::Constructor(..)) =>
            {
                Self(callee.id)
            }
            TypedExprKind::Constructor(..) => Self(expr.id),
            _ => panic!(
                "CallSiteId::from_constructor called for non-constructor expression: {:?}",
                expr.kind
            ),
        }
    }

    pub fn from_variant(expr: &TypedExpr) -> Self {
        match &expr.kind {
            TypedExprKind::Call { callee, .. }
                if matches!(callee.kind, TypedExprKind::Member { .. }) =>
            {
                Self(callee.id)
            }
            TypedExprKind::Member { .. } => Self(expr.id),
            _ => panic!(
                "CallSiteId::from_variant called for non-variant expression: {:?}",
                expr.kind
            ),
        }
    }

    pub(crate) fn from_resolved_member_constraint(node_id: NodeID) -> Self {
        Self(node_id)
    }

    pub(crate) fn from_callee_node(node_id: NodeID) -> Self {
        Self(node_id)
    }

    pub(crate) fn from_lowered_source(node_id: NodeID) -> Self {
        Self(node_id)
    }

    pub fn node_id(self) -> NodeID {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CallerContext {
    Callable(Symbol),
    TopLevel,
}

impl CallerContext {
    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            CallerContext::Callable(symbol) => CallerContext::Callable(symbol.import(module_id)),
            CallerContext::TopLevel => CallerContext::TopLevel,
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

    pub fn same_receiver_source(&self, other: &Self) -> bool {
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

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MethodTarget {
    Concrete(Symbol),
    Requirement {
        protocol: Symbol,
        requirement: Symbol,
        label: Label,
    },
}

impl MethodTarget {
    pub fn symbol(&self) -> Symbol {
        match self {
            MethodTarget::Concrete(symbol) => *symbol,
            MethodTarget::Requirement { requirement, .. } => *requirement,
        }
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            MethodTarget::Concrete(symbol) => MethodTarget::Concrete(symbol.import(module_id)),
            MethodTarget::Requirement {
                protocol,
                requirement,
                label,
            } => MethodTarget::Requirement {
                protocol: protocol.import(module_id),
                requirement: requirement.import(module_id),
                label,
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CallEvidence {
    None,
    ConcreteWitness {
        conformance_key: ConformanceKey,
        witness: Symbol,
    },
    Deferred,
}

impl CallEvidence {
    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            CallEvidence::None => CallEvidence::None,
            CallEvidence::ConcreteWitness {
                conformance_key,
                witness,
            } => CallEvidence::ConcreteWitness {
                conformance_key: ConformanceKey {
                    protocol_id: conformance_key.protocol_id.import(module_id),
                    conforming_id: conformance_key.conforming_id.import(module_id),
                },
                witness: witness.import(module_id),
            },
            CallEvidence::Deferred => CallEvidence::Deferred,
        }
    }
}

pub type ResolvedCallSites = FxHashMap<CallSiteId, ResolvedCallSite>;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ResolvedCallSite {
    pub caller: CallerContext,
    pub kind: ResolvedCallSiteKind,
}

impl ResolvedCallSite {
    pub fn import(self, module_id: ModuleId) -> Self {
        Self {
            caller: self.caller.import(module_id),
            kind: self.kind.import(module_id),
        }
    }

    pub fn substitutions(&self) -> &CallSubstitutions {
        self.kind.substitutions()
    }

    pub fn target_symbol(&self) -> Symbol {
        self.kind.target_symbol()
    }

    pub fn receiver(&self) -> Option<&CallReceiver> {
        match &self.kind {
            ResolvedCallSiteKind::MethodCall { receiver, .. } => Some(receiver),
            _ => None,
        }
    }

    pub fn argument_plan(&self) -> CallArgumentPlan {
        match &self.kind {
            ResolvedCallSiteKind::MethodCall { argument_plan, .. } => argument_plan.clone(),
            _ => CallArgumentPlan::AsWritten,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ResolvedCallSiteKind {
    DirectCall {
        target: Symbol,
        substitutions: CallSubstitutions,
    },
    InitializerCall {
        nominal: Symbol,
        initializer: Symbol,
        substitutions: CallSubstitutions,
    },
    MethodCall {
        target: MethodTarget,
        receiver: CallReceiver,
        argument_plan: CallArgumentPlan,
        substitutions: CallSubstitutions,
        evidence: CallEvidence,
    },
    VariantConstructor {
        enum_symbol: Symbol,
        variant: Symbol,
        substitutions: CallSubstitutions,
    },
    EffectCall {
        effect: Symbol,
        substitutions: CallSubstitutions,
    },
}

impl ResolvedCallSiteKind {
    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            ResolvedCallSiteKind::DirectCall {
                target,
                substitutions,
            } => ResolvedCallSiteKind::DirectCall {
                target: target.import(module_id),
                substitutions: substitutions.import(module_id),
            },
            ResolvedCallSiteKind::InitializerCall {
                nominal,
                initializer,
                substitutions,
            } => ResolvedCallSiteKind::InitializerCall {
                nominal: nominal.import(module_id),
                initializer: initializer.import(module_id),
                substitutions: substitutions.import(module_id),
            },
            ResolvedCallSiteKind::MethodCall {
                target,
                receiver,
                argument_plan,
                substitutions,
                evidence,
            } => ResolvedCallSiteKind::MethodCall {
                target: target.import(module_id),
                receiver: receiver.import(module_id),
                argument_plan,
                substitutions: substitutions.import(module_id),
                evidence: evidence.import(module_id),
            },
            ResolvedCallSiteKind::VariantConstructor {
                enum_symbol,
                variant,
                substitutions,
            } => ResolvedCallSiteKind::VariantConstructor {
                enum_symbol: enum_symbol.import(module_id),
                variant: variant.import(module_id),
                substitutions: substitutions.import(module_id),
            },
            ResolvedCallSiteKind::EffectCall {
                effect,
                substitutions,
            } => ResolvedCallSiteKind::EffectCall {
                effect: effect.import(module_id),
                substitutions: substitutions.import(module_id),
            },
        }
    }

    pub fn substitutions(&self) -> &CallSubstitutions {
        match self {
            ResolvedCallSiteKind::DirectCall { substitutions, .. }
            | ResolvedCallSiteKind::InitializerCall { substitutions, .. }
            | ResolvedCallSiteKind::MethodCall { substitutions, .. }
            | ResolvedCallSiteKind::VariantConstructor { substitutions, .. }
            | ResolvedCallSiteKind::EffectCall { substitutions, .. } => substitutions,
        }
    }

    pub fn target_symbol(&self) -> Symbol {
        match self {
            ResolvedCallSiteKind::DirectCall { target, .. } => *target,
            ResolvedCallSiteKind::InitializerCall { initializer, .. } => *initializer,
            ResolvedCallSiteKind::MethodCall { target, .. } => target.symbol(),
            ResolvedCallSiteKind::VariantConstructor { variant, .. } => *variant,
            ResolvedCallSiteKind::EffectCall { effect, .. } => *effect,
        }
    }
}

pub type PendingResolvedCallSites = FxHashMap<CallSiteId, PendingResolvedCallSite>;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct PendingResolvedCallSite {
    pub caller: CallerContext,
    pub kind: PendingResolvedCallSiteKind,
}

impl PendingResolvedCallSite {
    pub fn record_method_shape(&mut self, shape: CallShape) {
        let Some(receiver) = shape.receiver else {
            return;
        };

        self.kind = match std::mem::replace(
            &mut self.kind,
            PendingResolvedCallSiteKind::MemberAccess {
                label: Label::Named("<invalid>".into()),
                target_candidates: vec![],
            },
        ) {
            PendingResolvedCallSiteKind::MemberAccess {
                label,
                target_candidates,
            } => PendingResolvedCallSiteKind::MethodCall {
                label,
                target_candidates,
                receiver,
                argument_plan: shape.argument_plan,
            },
            PendingResolvedCallSiteKind::MethodCall {
                label,
                target_candidates,
                receiver: existing,
                argument_plan,
            } => {
                let existing_shape = CallShape {
                    receiver: Some(existing.clone()),
                    argument_plan: argument_plan.clone(),
                };
                let new_shape = CallShape {
                    receiver: Some(receiver.clone()),
                    argument_plan: shape.argument_plan.clone(),
                };
                assert!(
                    existing_shape.same_receiver_source(&new_shape),
                    "conflicting call shapes recorded for one call site: {existing_shape:?} vs {new_shape:?}"
                );
                PendingResolvedCallSiteKind::MethodCall {
                    label,
                    target_candidates,
                    receiver,
                    argument_plan: shape.argument_plan,
                }
            }
            other => other,
        };
    }

    pub fn record_target(&mut self, target: CallTarget) {
        match &mut self.kind {
            PendingResolvedCallSiteKind::MethodCall {
                target_candidates, ..
            }
            | PendingResolvedCallSiteKind::MemberAccess {
                target_candidates, ..
            } => {
                if !target_candidates.contains(&target) {
                    target_candidates.push(target);
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PendingResolvedCallSiteKind {
    DirectCall {
        target: Symbol,
    },
    InitializerCall {
        nominal: Symbol,
    },
    MethodCall {
        label: Label,
        target_candidates: Vec<CallTarget>,
        receiver: CallReceiver,
        argument_plan: CallArgumentPlan,
    },
    MemberAccess {
        label: Label,
        target_candidates: Vec<CallTarget>,
    },
    EffectCall {
        effect: Symbol,
    },
}
