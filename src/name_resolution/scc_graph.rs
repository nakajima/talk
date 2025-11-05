use petgraph::{
    algo::kosaraju_scc,
    graph::{DiGraph, NodeIndex},
};
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{name_resolution::symbol::Symbol, node_id::NodeID, types::infer_ty::Level};

#[derive(Default, Debug, Clone, PartialEq)]
pub struct BindingGroup {
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
    pub fn rhs_id_for(&self, binder: &Symbol) -> &NodeID {
        self.rhs_ids.get(binder).unwrap()
    }

    pub fn groups(&self) -> Vec<BindingGroup> {
        kosaraju_scc(&self.graph)
            .iter()
            .map(|ids| {
                let mut level = Level::default();
                BindingGroup {
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

    pub fn add_node(&mut self, node: Symbol, rhs_id: NodeID, level: Level) -> NodeIndex {
        if let Some(idx) = self.idx_map.get(&node) {
            // Update stored level to the max of existing and new, so later
            // passes (with more accurate nesting) can raise the level.
            if let Some(existing) = self.level_map.get_mut(idx)
                && level > *existing
            {
                *existing = level;
            }
            // Update rhs_id if we didn't have one previously for this symbol.
            self.rhs_ids.entry(node).or_insert(rhs_id);
            return *idx;
        }

        let idx = self.graph.add_node(node);
        self.idx_map.insert(node, idx);
        self.rhs_ids.insert(node, rhs_id);
        self.level_map.insert(idx, level);
        idx
    }

    #[instrument(skip(self))]
    pub fn add_edge(&mut self, from: (Symbol, NodeID), to: (Symbol, NodeID), node_id: NodeID) {
        if from.0 == to.0 {
            return;
        }
        let from = self.add_node(from.0, from.1, Level::default());
        let to = self.add_node(to.0, to.1, Level::default());
        self.graph.update_edge(from, to, node_id);
    }
}
