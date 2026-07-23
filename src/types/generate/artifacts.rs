use super::*;

#[derive(Default)]
pub(super) struct TypeArtifacts {
    pub(super) node_types: FxHashMap<NodeID, Ty>,
    pub(super) instantiations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    pub(super) member_resolutions: FxHashMap<NodeID, MemberResolution>,
    pub(super) integer_literals: FxHashMap<NodeID, CheckedIntegerLiteral>,
    pub(super) for_plans: FxHashMap<NodeID, ForPlan>,
    pub(super) propagation_plans: FxHashMap<NodeID, PropagationPlan>,
    pub(super) coerce_clones: FxHashSet<NodeID>,
    /// Mode-marked call arguments awaiting the post-solve marker checks
    /// (ADR 0038): `copy` demands Copy or CheapClone evidence; `mut` and
    /// `borrow` must agree with the callee's parameter mode.
    pub(super) marked_args: Vec<(NodeID, MarkedSlot, crate::parsing::node_kinds::call_arg::ArgMode)>,
    pub(super) existential_packs: FxHashMap<NodeID, ExistentialPack>,
    pub(super) checked_ir: FxHashMap<NodeID, crate::types::output::CheckedIrKind>,
    pub(super) effect_contracts: FxHashMap<NodeID, crate::types::output::EffectContract>,
    /// Each checked pattern occurrence's type (pre-view: binders keep
    /// their borrows), keyed by pattern node — record-field slots
    /// included, keyed by the field node (ADR 0038).
    pub(super) pattern_tys: FxHashMap<NodeID, Ty>,
    /// Per struct pattern: one slot per stored field in declaration
    /// order — instantiated type and the covering sub-pattern node
    /// (ADR 0038).
    pub(super) struct_pattern_slots: FxHashMap<NodeID, Vec<(Ty, Option<NodeID>)>>,
    /// Per record pattern: the written field labels and nodes, in
    /// pattern order. Finalize assembles the row-layout slot table from
    /// these once the row has solved (ADR 0038).
    pub(super) record_pattern_labels: FxHashMap<NodeID, Vec<(String, NodeID)>>,
    pub(super) display_names: FxHashMap<Symbol, String>,
    /// Descending per-file id mint for checker-owned nodes (a `for`
    /// statement's implicit `iter()`/`next()` calls). Parser ids ascend
    /// from zero, so the ranges never meet; the low-water mark is
    /// published as `TypeOutput::synthetic_floors` so the typed-tree
    /// build keeps minting below it.
    pub(super) synthetic_next: FxHashMap<crate::node_id::FileID, u32>,
}

/// How a marked argument's parameter slot resolves after solving. In
/// checking mode the parameter type is in hand; through an unresolved
/// callee (member calls, in-flight bindings) the slot is found by
/// indexing the callee's solved function type, right-aligned so a
/// receiver-less member type still lines up.
pub(super) enum MarkedSlot {
    /// The parameter type the argument checked against.
    Param(Ty),
    /// The `index`th of `arg_count` written arguments of `callee`;
    /// `arg_ty` is the argument's own inferred type (the value a `copy`
    /// marker clones).
    CalleeIndexed {
        callee: Ty,
        index: usize,
        arg_count: usize,
        arg_ty: Ty,
    },
}

impl<'s, 'a> BodyChecker<'s, 'a> {
    /// Records the signed 64-bit value of every integer literal, or an
    /// explicit recovery so one bad literal produces one diagnostic
    /// (ledger row LIT-01).
    pub(super) fn check_integer_literal(&mut self, node: NodeID, source: &str) {
        let normalized = source.replace('_', "");
        let checked = match normalized.parse::<i64>() {
            Ok(value) => CheckedIntegerLiteral::Value(value),
            Err(_) => {
                self.diagnostics.errors.push((
                    TypeError::IntegerLiteralOutOfRange {
                        literal: source.into(),
                    },
                    node,
                ));
                CheckedIntegerLiteral::Invalid
            }
        };
        self.artifacts.integer_literals.insert(node, checked);
    }
}

impl TypeArtifacts {
    pub(super) fn synthetic_id(&mut self, file: crate::node_id::FileID) -> NodeID {
        let next = self.synthetic_next.entry(file).or_insert(u32::MAX);
        *next -= 1;
        NodeID(file, *next)
    }
}
