//! The nesting tree — the relaxed, free-variable-based analogue of the
//! dominator tree (Leißa & Griebler §4). Construction follows Fig. 8:
//! BFS over local functions; each newly discovered function attaches at the
//! deepest already-placed ancestor whose variable occurs free in it.
//! Sibling dependencies (Rule SIBL, §4.1.1) + per-level Tarjan SCCs
//! (Tarjan, SIAM J. Comput. 1972) recover loops and (mutual) recursion —
//! including irreducible control flow with no special handling (§4.1.2).
//! The virtual root (§4.1.2) makes a single forest of the whole program,
//! whose top-level sibling dependencies are the call graph.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::lambda_g::program::{Label, Program};

#[derive(Debug)]
pub struct NestingTree {
    /// inest (paper Eq. 21): immediate nester; None = root of the forest.
    parents: FxHashMap<Label, Option<Label>>,
    /// Members of a sibling-dependency cycle (direct or mutual recursion).
    cyclic: FxHashSet<Label>,
    /// Discovery order (stable traversal order for consumers).
    pub order: Vec<Label>,
}

impl NestingTree {
    pub fn parent(&self, label: Label) -> Option<Label> {
        self.parents.get(&label).copied().flatten()
    }

    pub fn contains(&self, label: Label) -> bool {
        self.parents.contains_key(&label)
    }

    pub fn in_cycle(&self, label: Label) -> bool {
        self.cyclic.contains(&label)
    }

    pub fn children(&self, label: Option<Label>) -> Vec<Label> {
        self.order
            .iter()
            .copied()
            .filter(|l| self.parents.get(l).copied().flatten() == label)
            .collect()
    }
}

impl Program {
    /// Fig. 8, single root.
    pub fn nesting_tree(&mut self, root: Label) -> NestingTree {
        self.build_nesting(vec![root])
    }

    /// §4.1.2's virtual root: closed functions (FV = ∅) are the forest's
    /// roots; the whole reachable program hangs beneath them.
    pub fn nesting_forest(&mut self) -> NestingTree {
        let mut roots = vec![];
        for label in self.labels().collect::<Vec<_>>() {
            let fv = self.fv(label);
            if self.set_labels(fv).is_empty() {
                roots.push(label);
            }
        }
        self.build_nesting(roots)
    }

    fn build_nesting(&mut self, roots: Vec<Label>) -> NestingTree {
        let mut tree = NestingTree {
            parents: FxHashMap::default(),
            cyclic: FxHashSet::default(),
            order: vec![],
        };
        let mut queue: std::collections::VecDeque<Label> = std::collections::VecDeque::new();
        for root in roots {
            if let std::collections::hash_map::Entry::Vacant(entry) = tree.parents.entry(root) {
                entry.insert(None);
                tree.order.push(root);
                queue.push_back(root);
            }
        }

        while let Some(n) = queue.pop_front() {
            let Some(body) = self.body(n) else { continue };
            let locals = self.set_labels(self.expr(body).lf);
            for l in locals {
                if tree.parents.contains_key(&l) {
                    continue;
                }
                // Walk up from the discovering node to the deepest ancestor
                // whose variable is free in ℓ (Fig. 8's inner loop).
                let fv_l = self.fv(l);
                let mut parent = Some(n);
                let mut chosen: Option<Label> = None;
                while let Some(p) = parent {
                    if self.sets.contains(fv_l, p) {
                        chosen = Some(p);
                        break;
                    }
                    parent = tree.parents.get(&p).copied().flatten();
                }
                tree.parents.insert(l, chosen);
                tree.order.push(l);
                queue.push_back(l);
            }
        }

        self.mark_cycles(&mut tree);
        tree
    }

    /// Sibling dependencies (Rule SIBL) + Tarjan per nesting level
    /// (§4.1.1–4.1.2): an edge ℓ1 → ℓ2 between siblings exists when some
    /// function nested in ℓ1 references ℓ2. Cycles = recursion; self-loops =
    /// direct recursion.
    fn mark_cycles(&mut self, tree: &mut NestingTree) {
        // Ancestor-at-level lookup: for u and a target parent p, find the
        // ancestor of u whose parent is p.
        let ancestor_at = |tree: &NestingTree, mut u: Label, p: Option<Label>| -> Option<Label> {
            loop {
                let up = tree.parents.get(&u).copied().flatten();
                if up == p {
                    return Some(u);
                }
                u = up?;
            }
        };

        // Collect sibling edges per parent.
        let mut edges: FxHashMap<Option<Label>, Vec<(Label, Label)>> = FxHashMap::default();
        for &u in &tree.order {
            let Some(body) = self.body(u) else { continue };
            for target in self.set_labels(self.expr(body).lf) {
                if !tree.contains(target) {
                    continue;
                }
                let p = tree.parents.get(&target).copied().flatten();
                if let Some(source_sibling) = ancestor_at(tree, u, p) {
                    edges.entry(p).or_default().push((source_sibling, target));
                }
            }
        }

        // Tarjan per level via petgraph.
        for (_, level_edges) in edges {
            use petgraph::algo::tarjan_scc;
            use petgraph::graph::DiGraph;
            let mut graph = DiGraph::<Label, ()>::new();
            let mut index = FxHashMap::default();
            for &(a, b) in &level_edges {
                for node in [a, b] {
                    index.entry(node).or_insert_with(|| graph.add_node(node));
                }
            }
            let mut has_self_loop = FxHashSet::default();
            for (a, b) in level_edges {
                if a == b {
                    has_self_loop.insert(a);
                }
                graph.add_edge(index[&a], index[&b], ());
            }
            for scc in tarjan_scc(&graph) {
                if scc.len() > 1 {
                    for node in scc {
                        tree.cyclic.insert(graph[node]);
                    }
                } else if let [single] = scc.as_slice()
                    && has_self_loop.contains(&graph[*single])
                {
                    tree.cyclic.insert(graph[*single]);
                }
            }
        }
    }
}
