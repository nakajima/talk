use std::collections::HashMap;

use crate::{
    expr::Expr,
    parse_tree::ParseTree,
    parser::NodeID,
};

#[derive(Clone, Default, PartialEq, Debug)]
pub struct TypeVarID(u32);

#[derive(Debug)]
pub enum Constraint {
    Equality(NodeID, Ty, Ty),
}

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    Int,
    Float,
    Func(NodeID /* params */, NodeID /* returning */),
    TypeVar(TypeVarID),
    Tuple(Vec<usize>),
}

pub struct TypeChecker {
    pub parse_tree: ParseTree,
    pub environment: Option<Environment>,
}

#[derive(Default)]
pub struct Environment {
    pub types: HashMap<NodeID, Ty>,
    pub type_var_id: TypeVarID,
    pub constraints: Vec<Constraint>,
    pub type_stack: Vec<Ty>
}

impl Environment {
    pub fn new() -> Self {
        Self {
            types: HashMap::new(),
            type_var_id: TypeVarID(0),
            constraints: vec![],
            type_stack: vec![]
        }
    }

    fn new_type_variable(&mut self) -> Ty {
        self.type_var_id = TypeVarID(self.type_var_id.0 + 1);
        Ty::TypeVar(self.type_var_id.clone())
    }
}

impl TypeChecker {
    pub fn new(parse_tree: ParseTree) -> Self {
        Self {
            parse_tree,
            environment: None,
        }
    }

    pub fn infer(&mut self) {
        let mut env = Environment::new();

        for node in self.parse_tree.root_ids() {
            self.infer_node(node, &mut env);
        }

        self.environment = Some(env);
    }

    pub fn infer_node(&self, id: NodeID, env: &mut Environment) {
        match &self.parse_tree.get(id).unwrap(){
            Expr::LiteralInt(_) => {
                env.types.insert(id, Ty::Int);
            }
            Expr::LiteralFloat(_) => {
                env.types.insert(id, Ty::Float);
            }
            Expr::Func(name, params, body) => {
                self.infer_node(*params, env);
                self.infer_node(*body, env);
                env.types.insert(id, Ty::Func(*params, *body));
            }
            Expr::ResolvedVariable(_) => todo!("ResolvedVariable"),
            Expr::Variable(_) => todo!(
                "unresolved variable: {:?}",
                self.parse_tree.get(id).unwrap()
            ),
            _ => todo!(
                "not handling this yet: {:?}",
                &self.parse_tree.get(id).unwrap()
            ),
        }
    }

    pub fn type_for(&self, node_id: NodeID) -> Option<Ty> {
        let Some(env) = &self.environment else {
            panic!("no inference performed");
        };

        env.types.get(&node_id).cloned()
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
        let root_id = checker.parse_tree.root_ids()[0];

        let Some(Ty::Func(params, returning)) = checker.type_for(root_id) else {
            panic!("didnt get a func, got: {:#?}", checker.type_for(root_id));
        };

        let params_type = checker.type_for(params);
        let return_type = checker.type_for(returning);

        assert_eq!(return_type, params_type);

        // assert_eq!(params_types[0], Ty::TypeVar(1));
        // assert_eq!(return_type, Ty::Float);
    }
}
