use super::expr::Expr;

#[derive(Default)]
pub struct ParseTree {
    pub root: usize,
    nodes: Vec<Expr>,
}

impl ParseTree {
    pub fn new() -> Self {
        Self {
            root: 0,
            nodes: vec![],
        }
    }

    pub fn add(&mut self, expr: Expr) -> usize {
        self.nodes.push(expr);
        self.nodes.len() - 1
    }

    pub fn root(&self) -> Option<&Expr> {
        println!("self.root = {}", self.root);
        println!("nodes = {:?}", self.nodes);
        if self.nodes.len() <= self.root {
            None
        } else {
            Some(&self.nodes[self.root])
        }
    }
}
