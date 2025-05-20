use super::{
    expr::{Expr, ExprMeta},
    parser::ExprID,
};

#[derive(Default, Debug, Clone)]
pub struct ParseTree {
    roots: Vec<ExprID>,
    pub(crate) nodes: Vec<Expr>,
    pub(crate) meta: Vec<ExprMeta>,
}

impl ParseTree {
    pub fn new() -> Self {
        Self {
            roots: vec![],
            nodes: vec![],
            meta: vec![],
        }
    }

    // Adds the expr to the parse tree and sets its ID
    pub fn add(&mut self, expr: Expr, meta: ExprMeta) -> ExprID {
        let id = self.nodes.len() as ExprID;
        self.nodes.push(expr);
        self.meta.push(meta);
        id
    }

    pub fn push_root(&mut self, root: ExprID) {
        self.roots.push(root);
    }

    // Gets the root expr of the tree
    pub fn roots(&self) -> Vec<Option<&Expr>> {
        self.roots.iter().map(|r| self.get(*r)).collect()
    }

    // Gets the root expr of the tree
    pub fn root_ids(&self) -> Vec<ExprID> {
        self.roots.clone()
    }

    // Gets the expr at a given index
    pub fn get(&self, index: ExprID) -> Option<&Expr> {
        let index = index as usize;

        if self.nodes.len() <= index {
            None
        } else {
            Some(&self.nodes[index])
        }
    }

    // Gets the expr at a given index
    pub fn get_mut(&mut self, index: ExprID) -> Option<&mut Expr> {
        let index = index as usize;

        if self.nodes.len() <= index {
            None
        } else {
            Some(&mut self.nodes[index])
        }
    }
}
