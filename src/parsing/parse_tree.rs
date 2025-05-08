use super::{
    expr::{Expr, ExprKind},
    visitor::Visitor,
};

#[derive(Default, Debug, Clone)]
pub struct ParseTree {
    roots: Vec<usize>,
    pub(crate) nodes: Vec<Expr>,
}

impl ParseTree {
    pub fn new() -> Self {
        Self {
            roots: vec![],
            nodes: vec![],
        }
    }

    pub fn visit<C, R>(&self, visitor: &impl Visitor<R, C>, context: &C) -> Vec<R> {
        self.roots()
            .iter()
            .filter_map(|root| *root)
            .map(|root| self.accept(root, visitor, context))
            .collect()
    }

    pub fn accept<C, R>(&self, expr: &Expr, visitor: &impl Visitor<R, C>, context: &C) -> R {
        match &expr.kind {
            ExprKind::Binary(lhs, op, rhs) => visitor.visit_binary_expr(
                self.get(*lhs).expect("index not in parse tree"),
                self.get(*rhs).expect("index not in parse tree"),
                *op,
                context,
                self,
            ),
            ExprKind::Unary(op, rhs) => visitor.visit_unary_expr(
                self.get(*rhs).expect("index not in parse tree"),
                *op,
                context,
                self,
            ),
            ExprKind::LiteralInt(val) => visitor.visit_literal_int(val, context, self),
            ExprKind::LiteralFloat(val) => visitor.visit_literal_float(val, context, self),
            ExprKind::Variable(val) => visitor.visit_variable(val, context, self),
            ExprKind::Tuple(items) => visitor.visit_tuple(items.clone(), context, self),
            ExprKind::EmptyTuple => visitor.visit_tuple(vec![], context, self),
            ExprKind::Block(_exprs) => todo!(),
            ExprKind::Func(func) => visitor.visit_func(func.clone(), context, self),
        }
    }

    // Adds the expr to the parse tree and sets its ID
    pub fn add(&mut self, mut expr: Expr) -> usize {
        let id = self.nodes.len();
        expr.id = id;
        self.nodes.push(expr);
        id
    }

    pub fn push_root(&mut self, root: usize) {
        self.roots.push(root);
    }

    // Gets the root expr of the tree
    pub fn roots(&self) -> Vec<Option<&Expr>> {
        self.roots.iter().map(|r| self.get(*r)).collect()
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
