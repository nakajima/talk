use std::collections::HashMap;

use crate::{expr::Expr, parse_tree::ParseTree, parser::NodeID, token::Token};

use super::constraint_solver::ConstraintSolver;

#[derive(Clone, Copy, Default, PartialEq, Debug, Eq, Hash)]
pub struct TypeVarID(u32);

#[derive(Debug, Clone)]
pub enum Constraint {
    Equality(NodeID, Ty, Ty),
}

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    Int,
    Float,
    Func(Vec<NodeID> /* params */, NodeID /* returning */),
    TypeVar(TypeVarID),
    Tuple(Vec<NodeID>),
}

pub struct TypeChecker {
    pub parse_tree: ParseTree,
    pub environment: Option<Environment>,
}

#[derive(Default, Debug)]
pub struct Environment {
    pub types: HashMap<NodeID, Ty>,
    pub type_var_id: TypeVarID,
    pub constraints: Vec<Constraint>,
    pub type_stack: Vec<Ty>,
    pub type_counter_stack: Vec<u8>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            types: HashMap::new(),
            type_var_id: TypeVarID(0),
            constraints: vec![],
            type_stack: vec![],
            type_counter_stack: vec![],
        }
    }

    fn new_type_variable(&mut self) -> Ty {
        self.type_var_id = TypeVarID(self.type_var_id.0 + 1);
        Ty::TypeVar(self.type_var_id)
    }
}

impl TypeChecker {
    pub fn new(parse_tree: ParseTree) -> Self {
        Self {
            parse_tree,
            environment: None,
        }
    }

    pub fn define(&mut self, node_id: NodeID, ty: Ty) {
        self.environment
            .as_mut()
            .expect("type inference not performed")
            .types
            .insert(node_id, ty);
    }

    pub fn infer(&mut self) {
        let mut env = Environment::new();

        for node in self.parse_tree.root_ids() {
            self.infer_node(node, &mut env);
        }

        self.environment = Some(env);
    }

    pub fn resolve(&mut self) {
        let mut constraints = self.environment.as_ref().unwrap().constraints.clone();
        let mut resolver = ConstraintSolver::new(self, &mut constraints);
        resolver.solve();
    }

    pub fn infer_node(&self, id: NodeID, env: &mut Environment) -> Ty {
        match &self.parse_tree.get(id).unwrap() {
            Expr::LiteralInt(_) => {
                env.types.insert(id, Ty::Int);
                Ty::Int
            }
            Expr::LiteralFloat(_) => {
                env.types.insert(id, Ty::Float);
                Ty::Float
            }
            Expr::Assignment(lhs, rhs) => {
                let lhs_ty = self.infer_node(*lhs, env);
                let rhs_ty = self.infer_node(*rhs, env);

                env.constraints
                    .push(Constraint::Equality(*lhs, lhs_ty.clone(), rhs_ty));

                lhs_ty
            }
            Expr::Let(name) => {
                let ty = env.new_type_variable();
                env.types.insert(id, ty.clone());
                env.type_stack.push(ty.clone());
                ty
            }
            Expr::Func(name, params, body) => {
                self.start_func(*name, params, *body, env);
                self.infer_node(*body, env);
                self.end_func(env);
                env.types.insert(id, Ty::Func(params.clone(), *body));
                Ty::Func(params.clone(), *body)
            }
            Expr::ResolvedVariable(depth) => {
                let ty = &env.type_stack[env.type_stack.len() - 1 - *depth as usize];
                env.types.insert(id, ty.clone());
                ty.clone()
            }
            Expr::Parameter(_) => todo!(
                "unresolved parameter: {:?}",
                self.parse_tree.get(id).unwrap()
            ),
            Expr::Variable(_) => todo!(
                "unresolved variable: {:?}",
                self.parse_tree.get(id).unwrap()
            ),
            Expr::Tuple(items) => Ty::Tuple(items.clone()),
            Expr::Unary(_token_kind, _) => todo!(),
            Expr::Binary(_, _token_kind, _) => todo!(),
            Expr::Block(items) => {
                for item in items {
                    self.infer_node(*item, env);
                }

                let return_ty = if let Some(last_id) = items.last() {
                    env.types.get(last_id).unwrap().clone()
                } else {
                    Ty::Tuple(vec![])
                };

                env.types.insert(id, return_ty.clone());
                return_ty
            }
        }
    }

    pub fn start_func(
        &self,
        name: Option<Token>,
        param_ids: &Vec<NodeID>,
        body: NodeID,
        env: &mut Environment,
    ) {
        if name.is_some() {
            let name_type = Ty::Func(param_ids.clone(), body);
            env.type_stack.push(name_type);
        }

        let type_counter = param_ids.len() as u8;

        env.type_counter_stack.push(type_counter);

        for param_id in param_ids {
            let param_var = env.new_type_variable();
            env.types.insert(*param_id, param_var.clone());
            env.type_stack.push(param_var);
        }
    }

    fn end_func(&self, env: &mut Environment) {
        let depth = env
            .type_counter_stack
            .pop()
            .expect("trying to pop empty type counter?");

        for _ in 0..depth {
            env.type_stack.pop();
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
    use crate::{
        name_resolver::NameResolver,
        parser::parse,
        type_checker::{Ty, TypeVarID},
    };

    use super::TypeChecker;

    fn check(code: &'static str) -> TypeChecker {
        let parsed = parse(code).unwrap();
        let mut resolver = NameResolver::new();
        let resolved = resolver.resolve(parsed);
        let mut checker = TypeChecker::new(resolved);
        checker.infer();
        checker.resolve();
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
        let checker = check("func sup(name) { name }\nsup");
        let root_id = checker.parse_tree.root_ids()[0];

        let Some(Ty::Func(params, returning)) = checker.type_for(root_id) else {
            panic!("didnt get a func, got: {:#?}", checker.type_for(root_id));
        };

        let param_type = checker.type_for(params[0]);
        let return_type = checker.type_for(returning);

        assert_eq!(return_type, param_type);
        assert_eq!(return_type.unwrap(), Ty::TypeVar(TypeVarID(1)));
        // assert_eq!(return_type, Ty::Float);

        assert_eq!(
            checker.type_for(checker.parse_tree.root_ids()[1]),
            Some(Ty::Func(params, returning))
        );
    }

    #[test]
    fn checks_a_let_assignment() {
        let checker = check("let count = 123\ncount");
        let root_id = checker.parse_tree.root_ids()[1];
        assert_eq!(checker.type_for(root_id), Some(Ty::Int));
    }
}
