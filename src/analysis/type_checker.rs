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

pub struct TypeChecker {
    pub parse_tree: ParseTree,
    pub environment: Option<Environment>
}

pub struct Environment {
    pub types: Vec<Option<Ty>>,
    pub type_var_id: TypeVarID,
    pub constraints: Vec<Constraint>,
}

impl Environment {
    pub fn new(size: usize) -> Self {
        let mut env = Self {
            types: Vec::with_capacity(size),
            type_var_id: 0,
            constraints: vec![],
        };

        for _ in 0..size {
            env.types.push(None);
        }

        env
    }

    fn new_type_variable(&mut self) -> (TypeVarID, Ty) {
        self.type_var_id += 1;
        (self.type_var_id, Ty::TypeVar(self.type_var_id))
    }
}

impl TypeChecker {
    pub fn new(parse_tree: ParseTree) -> Self {
        Self { parse_tree, environment: None }
    }

    pub fn infer(&mut self) {
        let mut env = Environment::new(self.parse_tree.nodes.len());

        for node in self.parse_tree.nodes.iter() {
            let mut result = self.infer_node(node, &mut env);
            env.types[node.id as usize] = result.typed;
            env.constraints.append(&mut result.constraints);
        }

        self.environment = Some(env);
    }

    pub fn infer_node(&self, node: &Expr, env: &mut Environment) -> InferenceResult {
        match &self.parse_tree.get(node.id).unwrap().kind {
            ExprKind::LiteralInt(_) => InferenceResult::new(vec![], Some(Ty::Int)),
            ExprKind::LiteralFloat(_) => InferenceResult::new(vec![], Some(Ty::Float)),
            ExprKind::Func(_, params, body) => self.func(*params, *body, env),
            _ => todo!(
                "not handling this yet: {:?}",
                &self.parse_tree.get(node.id).unwrap().kind
            ),
        }
    }

    fn func(&self, params: NodeID, body: NodeID, env: &mut Environment) -> InferenceResult {
        let (params_id, params_type) = env.new_type_variable();
        env.types[params as usize] = Some(params_type);

        let (return_id, return_type) = env.new_type_variable();
        env.types[body as usize] = Some(return_type);

        InferenceResult::new(vec![], Some(Ty::Func(params_id, return_id)))
    }

    pub fn type_for(&self, node_id: NodeID) -> Option<Ty> {
        let Some(env) = &self.environment else { panic!("no inference performed"); };

        let node_id = node_id as usize;

        if env.types.len() <= node_id {
            None
        } else {
            env.types[node_id]
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{name_resolver::NameResolver, parser::parse, type_checker::Ty};

    use super::TypeChecker;

    fn check(code: &'static str) -> TypeChecker {
        let parsed = parse(code).unwrap();
        let mut resolver = NameResolver::new();
        let resolved = resolver.resolve(parsed);
        let mut checker = TypeChecker::new(resolved);
        checker.infer();
        checker
    }

    #[test]
    fn checks_an_int() {
        let parsed = parse("123").unwrap();
        let mut checker = TypeChecker::new(parsed);
        checker.infer();
        assert_eq!(checker.type_for(0).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_a_float() {
        let parsed = parse("123.").unwrap();
        let mut checker = TypeChecker::new(parsed);
        checker.infer();
        assert_eq!(checker.type_for(0).unwrap(), Ty::Float);
    }

    #[test]
    fn checks_a_func() {
        let checker = check("func sup(name) { name }");

        let root_id = checker.parse_tree.roots()[0].unwrap().id;
        assert_eq!(checker.type_for(root_id).unwrap(), Ty::Float);
    }
}
