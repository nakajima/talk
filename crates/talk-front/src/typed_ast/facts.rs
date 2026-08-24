//! Editor-facing per-node facts, collected in one walk over the typed
//! tree. This is an index into the one authority (ADR 0057): it is
//! rebuilt whenever the tree is, and it copies nothing the tree does not
//! carry — a fact missing here is missing from the tree, never merely
//! stale. Editor analysis resolves source NodeIDs against this instead of
//! the checker's retired NodeID tables.

use derive_visitor::{Drive, Visitor};
use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;
use crate::node_id::NodeID;
use crate::types::output::MemberResolution;
use crate::types::ty::Ty;

#[derive(Default, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct NodeFacts {
    /// Type of every expression and parameter node.
    pub node_types: FxHashMap<NodeID, Ty>,
    pub member_resolutions: FxHashMap<NodeID, MemberResolution>,
    pub instantiations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    pub selected_callables: FxHashMap<NodeID, Symbol>,
}

impl NodeFacts {
    /// The editor-relevant slice of a blocked file's elaboration. A file
    /// with errors builds no typed tree, so — for those files only — the
    /// checker's per-node decisions are kept in index form; each file has
    /// exactly one home for its facts (tree files never appear here).
    pub fn from_blocked_elaboration(
        elaboration: &crate::types::output::Elaboration,
        blocked: &rustc_hash::FxHashSet<crate::node_id::FileID>,
    ) -> Self {
        let keep = |id: &NodeID| blocked.contains(&id.0);
        NodeFacts {
            node_types: elaboration
                .node_types
                .iter()
                .filter(|(id, _)| keep(id))
                .map(|(id, ty)| (*id, ty.clone()))
                .collect(),
            member_resolutions: elaboration
                .member_resolutions
                .iter()
                .filter(|(id, _)| keep(id))
                .map(|(id, r)| (*id, r.clone()))
                .collect(),
            instantiations: elaboration
                .instantiations
                .iter()
                .filter(|(id, _)| keep(id))
                .map(|(id, i)| (*id, i.clone()))
                .collect(),
            selected_callables: elaboration
                .selected_callables
                .iter()
                .filter(|(id, _)| keep(id))
                .map(|(id, s)| (*id, *s))
                .collect(),
        }
    }

    /// Merge another index in (used to overlay blocked-file facts onto
    /// the tree-collected index; the key spaces are disjoint by
    /// construction).
    pub fn extend(&mut self, other: NodeFacts) {
        self.node_types.extend(other.node_types);
        self.member_resolutions.extend(other.member_resolutions);
        self.instantiations.extend(other.instantiations);
        self.selected_callables.extend(other.selected_callables);
    }
    pub fn collect<'a>(files: impl Iterator<Item = &'a super::TypedFile>) -> Self {
        #[derive(Visitor)]
        #[visitor(
            super::Expr(enter),
            super::Pattern(enter),
            super::Parameter(enter)
        )]
        struct Collect {
            facts: NodeFacts,
        }
        impl Collect {
            fn enter_expr(&mut self, expr: &super::Expr) {
                self.facts.node_types.insert(expr.id, expr.ty.clone());
                if let Some(resolution) = &expr.member_resolution {
                    self.facts
                        .member_resolutions
                        .insert(expr.id, resolution.clone());
                }
                if let Some(instantiation) = &expr.instantiation {
                    self.facts
                        .instantiations
                        .insert(expr.id, instantiation.clone());
                }
                if let Some(callable) = expr.selected_callable {
                    self.facts.selected_callables.insert(expr.id, callable);
                }
            }
            fn enter_pattern(&mut self, pattern: &super::Pattern) {
                // Variant patterns keep only the direct resolution on the
                // tree; the editor consumers match exactly that case.
                if let super::PatternKind::Variant {
                    resolved: Some(variant),
                    ..
                } = &pattern.kind
                {
                    self.facts
                        .member_resolutions
                        .insert(pattern.id, MemberResolution::Direct(*variant));
                }
            }
            fn enter_parameter(&mut self, param: &super::Parameter) {
                if let Some(ty) = &param.ty {
                    self.facts.node_types.insert(param.id, ty.clone());
                }
            }
        }

        let mut collect = Collect {
            facts: NodeFacts::default(),
        };
        let mut grafted: Vec<(NodeID, NodeID)> = Vec::new();
        for file in files {
            for root in &file.roots {
                root.drive(&mut collect);
            }
            grafted.extend_from_slice(&file.grafted);
        }
        let mut facts = collect.facts;
        // A grafted wrapper adopted its inner node's place in the tree;
        // queries at the erased inner id resolve to the wrapper's facts.
        for (inner, wrapper) in grafted {
            if let Some(ty) = facts.node_types.get(&wrapper).cloned() {
                facts.node_types.entry(inner).or_insert(ty);
            }
            if let Some(resolution) = facts.member_resolutions.get(&wrapper).cloned() {
                facts.member_resolutions.entry(inner).or_insert(resolution);
            }
            if let Some(instantiation) = facts.instantiations.get(&wrapper).cloned() {
                facts.instantiations.entry(inner).or_insert(instantiation);
            }
            if let Some(callable) = facts.selected_callables.get(&wrapper).copied() {
                facts.selected_callables.entry(inner).or_insert(callable);
            }
        }
        facts
    }
}
