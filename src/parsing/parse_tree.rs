use super::{
    expr::{Expr, ExprMeta},
    parser::NodeID,
    visitor::Visitor,
};

#[derive(Default, Debug, Clone)]
pub struct ParseTree {
    roots: Vec<NodeID>,
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

    pub fn visit<C, R>(&self, visitor: &impl Visitor<R, C>, context: &C) -> Vec<R> {
        self.roots()
            .iter()
            .filter_map(|root| *root)
            .map(|root| self.accept(root, visitor, context))
            .collect()
    }

    pub fn accept<C, R>(&self, expr: &Expr, visitor: &impl Visitor<R, C>, context: &C) -> R {
        match &expr {
            Expr::Binary(lhs, op, rhs) => visitor.visit_binary_expr(
                self.get(*lhs).expect("index not in parse tree"),
                self.get(*rhs).expect("index not in parse tree"),
                *op,
                context,
                self,
            ),
            Expr::Unary(op, rhs) => visitor.visit_unary_expr(
                self.get(*rhs).expect("index not in parse tree"),
                *op,
                context,
                self,
            ),
            Expr::LiteralInt(lexeme) => visitor.visit_literal_int(lexeme, context, self),
            Expr::LiteralFloat(lexeme) => visitor.visit_literal_float(lexeme, context, self),
            Expr::Variable(id) => visitor.visit_variable(id, context, self),
            Expr::Tuple(items) => visitor.visit_tuple(items.clone(), context, self),
            Expr::Block(_exprs) => todo!(),
            Expr::Func(name, params, body) => {
                visitor.visit_func(name, params, *body, context, self)
            }
            Expr::ResolvedVariable(_id) => todo!(),
            Expr::Parameter(_id) => todo!(),
            _ => todo!(),
        }
    }

    // Adds the expr to the parse tree and sets its ID
    pub fn add(&mut self, expr: Expr, meta: ExprMeta) -> NodeID {
        let id = self.nodes.len() as NodeID;
        self.nodes.push(expr);
        self.meta.push(meta);
        id
    }

    pub fn push_root(&mut self, root: NodeID) {
        self.roots.push(root);
    }

    // Gets the root expr of the tree
    pub fn roots(&self) -> Vec<Option<&Expr>> {
        self.roots.iter().map(|r| self.get(*r)).collect()
    }

    // Gets the root expr of the tree
    pub fn root_ids(&self) -> Vec<NodeID> {
        self.roots.clone()
    }

    // Gets the expr at a given index
    pub fn get(&self, index: NodeID) -> Option<&Expr> {
        let index = index as usize;

        if self.nodes.len() <= index {
            None
        } else {
            Some(&self.nodes[index])
        }
    }

    // Gets the expr at a given index
    pub fn get_mut(&mut self, index: NodeID) -> Option<&mut Expr> {
        let index = index as usize;

        if self.nodes.len() <= index {
            None
        } else {
            Some(&mut self.nodes[index])
        }
    }
}
