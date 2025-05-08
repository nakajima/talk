use super::{
    expr::{Expr, ExprKind},
    visitor::Visitor,
};

#[derive(Default, Debug, Clone)]
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

    pub fn accept<C, R>(&self, expr: &Expr, visitor: &impl Visitor<R, C>, context: C) -> R {
        match expr.kind {
            ExprKind::Binary(lhs, rhs, op) => visitor.visit_binary_expr(
                self.get(lhs).expect("index not in parse tree"),
                self.get(rhs).expect("index not in parse tree"),
                op,
                context,
                &self,
            ),
            ExprKind::Unary(rhs, op) => visitor.visit_unary_expr(
                self.get(rhs).expect("index not in parse tree"),
                op,
                context,
                &self,
            ),
            ExprKind::LiteralInt(val) => visitor.visit_literal_int(val, context, &self),
            ExprKind::LiteralFloat(val) => visitor.visit_literal_float(val, context, &self),
            ExprKind::Grouping(expr) => {
                let expr = self.get(expr).unwrap();
                self.accept(expr, visitor, context)
            }
            ExprKind::Variable(val) => visitor.visit_variable(val, context, &self),
        }
    }

    // Adds the expr to the parse tree and sets its ID
    pub fn add(&mut self, mut expr: Expr) -> usize {
        expr.id = self.nodes.len();
        self.nodes.push(expr);
        expr.id
    }

    // Gets the root expr of the tree
    pub fn root(&self) -> Option<&Expr> {
        if self.nodes.len() <= self.root {
            None
        } else {
            Some(&self.nodes[self.root])
        }
    }

    // Gets the expr at a given index
    pub fn get(&self, index: usize) -> Option<&Expr> {
        if self.nodes.len() <= index {
            None
        } else {
            Some(&self.nodes[index])
        }
    }
}
