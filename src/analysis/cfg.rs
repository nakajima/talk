use std::collections::{HashMap, HashSet};

use crate::lowering::lowerer::{BasicBlockID, IRFunction};

#[derive(Debug)]
pub struct ControlFlowGraph<'a> {
    pub func: &'a IRFunction,
    pub successors: HashMap<BasicBlockID, Vec<BasicBlockID>>,
    pub predecessors: HashMap<BasicBlockID, Vec<BasicBlockID>>,
    pub reverse_postorder: Vec<BasicBlockID>,
}

impl<'a> ControlFlowGraph<'a> {
    pub fn new(func: &'a IRFunction) -> Self {
        let mut successors = HashMap::new();
        let mut predecessors: HashMap<BasicBlockID, Vec<BasicBlockID>> = HashMap::new();

        for block in &func.blocks {
            successors.entry(block.id).or_default();
            predecessors.entry(block.id).or_default();
        }

        // Populate the maps by looking at the terminator of each block
        for block in &func.blocks {
            if let Some(terminator) = block.instructions.last() {
                let succs = terminator.successors(); // Use the method on `Instr`
                successors.insert(block.id, succs.clone());
                for &successor_id in &succs {
                    predecessors.entry(successor_id).or_default().push(block.id);
                }
            }
        }

        let reverse_postorder = Self::compute_reverse_postorder(func, &successors);

        Self {
            func,
            successors,
            predecessors,
            reverse_postorder,
        }
    }

    fn compute_reverse_postorder(
        func: &IRFunction,
        successors: &HashMap<BasicBlockID, Vec<BasicBlockID>>,
    ) -> Vec<BasicBlockID> {
        fn dfs_postorder(
            node: BasicBlockID,
            successors: &HashMap<BasicBlockID, Vec<BasicBlockID>>,
            visited: &mut HashSet<BasicBlockID>,
            postorder: &mut Vec<BasicBlockID>,
        ) {
            visited.insert(node);
            if let Some(succs) = successors.get(&node) {
                for &succ in succs {
                    if !visited.contains(&succ) {
                        dfs_postorder(succ, successors, visited, postorder);
                    }
                }
            }
            postorder.push(node);
        }

        let mut postorder = Vec::new();
        let mut visited = HashSet::new();
        // Start the traversal from the function's entry block.
        dfs_postorder(func.blocks[0].id, successors, &mut visited, &mut postorder);

        // The result of the traversal is a postorder list, so we reverse it.
        postorder.reverse();
        postorder
    }
}
