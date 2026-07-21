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
    pub(super) existential_packs: FxHashMap<NodeID, ExistentialPack>,
    pub(super) display_names: FxHashMap<Symbol, String>,
    /// Descending per-file id mint for checker-owned nodes (a `for`
    /// statement's implicit `iter()`/`next()` calls). Parser ids ascend
    /// from zero, so the ranges never meet; the low-water mark is
    /// published as `TypeOutput::synthetic_floors` so the typed-tree
    /// build keeps minting below it.
    pub(super) synthetic_next: FxHashMap<crate::node_id::FileID, u32>,
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
