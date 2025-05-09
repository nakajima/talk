use crate::{
    expr::{Expr, ExprKind},
    parse_tree::ParseTree,
    parser::NodeID,
};

type TypeID = u32;
type TypeVarID = u32;

#[derive(Debug)]
pub enum Constraint {
    Equality(NodeID, Ty, Ty),
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Ty {
    Int,
    Float,
    Func(TypeID /* params */, TypeID /* returning */),
    TypeVar(TypeVarID),
}

pub struct InferenceResult {
    constraints: Vec<Constraint>,
    typed: Option<Ty>,
}

impl InferenceResult {
    fn new(constraints: Vec<Constraint>, typed: Option<Ty>) -> Self {
        Self { constraints, typed }
    }
}

pub struct TypeChecker<'a> {
    pub parse_tree: &'a ParseTree,
    pub types: Vec<Option<Ty>>,
    pub type_var_id: TypeVarID,
    pub constraints: Vec<Constraint>,
}

impl<'a> TypeChecker<'a> {
    pub fn new(parse_tree: &'a ParseTree) -> Self {
        let mut checker = Self {
            parse_tree,
            types: Vec::with_capacity(parse_tree.nodes.len()),
            type_var_id: 0,
            constraints: vec![],
        };

        for _ in 0..parse_tree.nodes.len() {
            checker.types.push(None);
        }

        checker
    }

    pub fn infer(&mut self) {
        for node in &self.parse_tree.nodes {
            let mut result = self.infer_node(node);
            self.types[node.id as usize] = result.typed;
            self.constraints.append(&mut result.constraints);
        }
    }

    pub fn infer_node(&mut self, node: &Expr) -> InferenceResult {
        match &self.parse_tree.get(node.id).unwrap().kind {
            ExprKind::LiteralInt(_) => InferenceResult::new(vec![], Some(Ty::Int)),
            ExprKind::LiteralFloat(_) => InferenceResult::new(vec![], Some(Ty::Float)),
            ExprKind::Func(_, params, body) => self.func(*params, *body),
            _ => todo!(
                "not handling this yet: {:?}",
                &self.parse_tree.get(node.id).unwrap().kind
            ),
        }
    }

    fn func(&mut self, params: NodeID, body: NodeID) -> InferenceResult {
        let (params_id, params_type) = self.new_type_variable();
        self.types[params as usize] = Some(params_type);

        let (return_id, return_type) = self.new_type_variable();
        self.types[body as usize] = Some(return_type);

        InferenceResult::new(vec![], Some(Ty::Func(params_id, return_id)))
    }

    pub fn type_for(&self, node_id: NodeID) -> Option<Ty> {
        let node_id = node_id as usize;

        if self.types.len() <= node_id {
            None
        } else {
            self.types[node_id]
        }
    }

    fn new_type_variable(&mut self) -> (TypeVarID, Ty) {
        self.type_var_id += 1;
        (self.type_var_id, Ty::TypeVar(self.type_var_id))
    }
}

#[cfg(test)]
mod tests {
    use crate::{parser::parse, type_checker::Ty};

    use super::TypeChecker;

    #[test]
    fn checks_an_int() {
        let parsed = parse("123").unwrap();
        let mut checker = TypeChecker::new(&parsed);
        checker.infer();
        assert_eq!(checker.type_for(0).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_a_float() {
        let parsed = parse("123.").unwrap();
        let mut checker = TypeChecker::new(&parsed);
        checker.infer();
        assert_eq!(checker.type_for(0).unwrap(), Ty::Float);
    }

    #[test]
    fn checks_a_func() {
        let parsed = parse("func sup(name) { name }").unwrap();
        let mut checker = TypeChecker::new(&parsed);
        checker.infer();

        let root_id = parsed.roots()[0].unwrap().id;
        assert_eq!(checker.type_for(root_id).unwrap(), Ty::Float);
    }
}
