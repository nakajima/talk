use petgraph::{
    algo::kosaraju_scc,
    graph::{DiGraph, NodeIndex},
};
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{constraints::store::GroupId, infer_ty::Level},
};

#[derive(Default, Debug, Clone, PartialEq)]
pub struct BindingGroup {
    pub id: GroupId,
    pub level: Level,
    pub binders: Vec<Symbol>,
}

#[derive(Default, Debug, Clone)]
pub struct SCCGraph {
    pub(super) idx_map: FxHashMap<Symbol, NodeIndex>,
    pub graph: DiGraph<Symbol, NodeID>,
    rhs_ids: FxHashMap<Symbol, NodeID>,
    level_map: FxHashMap<NodeIndex, Level>,
}

impl SCCGraph {
    pub fn rhs_id_for(&self, binder: &Symbol) -> Option<&NodeID> {
        self.rhs_ids.get(binder)
    }

    pub fn groups(&self) -> Vec<BindingGroup> {
        kosaraju_scc(&self.graph)
            .iter()
            .enumerate()
            .map(|(i, ids)| {
                let mut level = Level::default();
                BindingGroup {
                    id: GroupId(i as u32),
                    binders: ids
                        .iter()
                        .map(|id| {
                            if self.level_map[id] > level {
                                level = self.level_map[id];
                            }
                            self.graph[*id]
                        })
                        .collect(),
                    level,
                }
            })
            .collect()
    }

    pub fn add_definition(&mut self, node: Symbol, rhs_id: NodeID, level: Level) -> NodeIndex {
        #[cfg(debug_assertions)]
        if matches!(node, Symbol::Builtin(..)) {
            unreachable!()
        }

        if let Some(idx) = self.idx_map.get(&node) {
            // Update stored level to the max of existing and new, so later
            // passes (with more accurate nesting) can raise the level.
            if let Some(existing) = self.level_map.get_mut(idx)
                && level > *existing
            {
                *existing = level;
            }
            // Only set rhs_id if not already set (by a previous definition).
            // This ensures the first definition wins, which is typically the actual declaration.
            self.rhs_ids.entry(node).or_insert(rhs_id);
            return *idx;
        }

        let idx = self.graph.add_node(node);
        self.idx_map.insert(node, idx);
        self.rhs_ids.insert(node, rhs_id);
        self.level_map.insert(idx, level);
        idx
    }

    fn ensure_node(&mut self, node: Symbol) -> NodeIndex {
        #[cfg(debug_assertions)]
        if matches!(node, Symbol::Builtin(..)) {
            unreachable!("should not have builtin in graph");
        }

        if let Some(idx) = self.idx_map.get(&node) {
            // Don't update anything for references if node already exists
            return *idx;
        }

        // First time seeing this symbol, and it's from a reference (forward reference).
        // Add the node but don't set rhs_id - let the definition set it later.
        let idx = self.graph.add_node(node);
        self.idx_map.insert(node, idx);
        self.level_map.insert(idx, Level::default());
        idx
    }

    #[instrument(skip(self))]
    pub fn add_edge(&mut self, from: (Symbol, NodeID), to: (Symbol, NodeID), node_id: NodeID) {
        if from.0 == to.0 {
            return;
        }
        let from = self.ensure_node(from.0);
        let to = self.ensure_node(to.0);
        self.graph.update_edge(from, to, node_id);
    }
}
