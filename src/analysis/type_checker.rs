use std::collections::HashMap;

use crate::{expr::Expr, parse_tree::ParseTree, parser::NodeID};

use super::constraint_solver::{ConstraintError, ConstraintSolver};

pub type FuncParams = Vec<Ty>;
pub type FuncReturning = Box<Ty>;

#[derive(Clone, Copy, Default, PartialEq, Debug, Eq, Hash)]
pub struct TypeVarID(u32);

#[derive(Debug, Clone)]
pub enum Constraint {
    Equality(NodeID, Ty, Ty),
}

#[derive(Debug, Clone, Copy)]
pub enum TypeError {}

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    Void,
    Int,
    Float,
    Func(
        FuncParams,    /* params */
        FuncReturning, /* returning */
    ),
    TypeVar(TypeVarID),
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

    pub fn start_scope(&mut self) {
        self.type_counter_stack.push(self.type_stack.len() as u8);
    }

    fn end_scope(&mut self) {
        let previous = self.type_counter_stack.pop().expect("no scope to end");

        while self.type_stack.len() as u8 > previous {
            self.type_stack.pop();
        }
    }

    fn new_type_variable(&mut self) -> Ty {
        self.type_var_id = TypeVarID(self.type_var_id.0 + 1);
        Ty::TypeVar(self.type_var_id)
    }
}

#[derive(Debug)]
pub struct TypeChecker {
    pub parse_tree: ParseTree,
    pub environment: Option<Environment>,
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

    pub fn infer(&mut self) -> Result<Vec<Ty>, TypeError> {
        let mut env = Environment::new();

        let typed_roots = self
            .parse_tree
            .root_ids()
            .iter()
            .map(|id| self.infer_node(*id, &mut env))
            .collect::<Result<Vec<_>, _>>()?;

        self.environment = Some(env);

        Ok(typed_roots)
    }

    pub fn resolve(&mut self) -> Result<(), ConstraintError> {
        let mut constraints = self.environment.as_ref().unwrap().constraints.clone();
        let mut resolver = ConstraintSolver::new(self, &mut constraints);
        resolver.solve()
    }

    pub fn infer_node(&self, id: NodeID, env: &mut Environment) -> Result<Ty, TypeError> {
        match &self.parse_tree.get(id).unwrap() {
            Expr::Call(callee, args) => {
                let callee_ty = self.infer_node(*callee, env)?;
                let param_vars: Vec<Ty> = args.iter().map(|_| env.new_type_variable()).collect();
                let ret_var = env.new_type_variable();

                env.constraints.push(Constraint::Equality(
                    *callee,
                    callee_ty.clone(),
                    Ty::Func(param_vars.clone(), Box::new(ret_var.clone())),
                ));

                for (arg_id, param_ty) in args.iter().zip(&param_vars) {
                    let actual = self.infer_node(*arg_id, env)?;
                    env.constraints
                        .push(Constraint::Equality(*arg_id, param_ty.clone(), actual));
                }

                env.types.insert(id, ret_var.clone());

                Ok(ret_var)
            }
            Expr::LiteralInt(_) => {
                env.types.insert(id, Ty::Int);
                Ok(Ty::Int)
            }
            Expr::LiteralFloat(_) => {
                env.types.insert(id, Ty::Float);
                Ok(Ty::Float)
            }
            Expr::Assignment(lhs, rhs) => {
                let lhs_ty = self.infer_node(*lhs, env)?;
                let rhs_ty = self.infer_node(*rhs, env)?;

                env.constraints
                    .push(Constraint::Equality(*lhs, lhs_ty.clone(), rhs_ty));

                Ok(lhs_ty)
            }
            Expr::Let(_name) => {
                let ty = env.new_type_variable();
                env.types.insert(id, ty.clone());
                env.type_stack.push(ty.clone());
                Ok(ty)
            }
            Expr::Func(name, params, body) => {
                env.start_scope();

                let mut param_vars: Vec<Ty> = vec![];
                for param_id in params {
                    let var_ty = env.new_type_variable();
                    env.types.insert(*param_id, var_ty.clone());
                    env.type_stack.push(var_ty.clone());

                    let actual = self.infer_node(*param_id, env)?;
                    env.constraints
                        .push(Constraint::Equality(*param_id, var_ty.clone(), actual));

                    param_vars.push(var_ty)
                }

                let body_var = env.new_type_variable();
                let body_ty = self.infer_node(*body, env)?;
                env.constraints
                    .push(Constraint::Equality(*body, body_var.clone(), body_ty));

                env.end_scope();

                let func_ty = Ty::Func(param_vars.clone(), FuncReturning::new(body_var.clone()));

                if name.is_some() {
                    env.type_stack.push(func_ty.clone());
                }

                env.types.insert(id, func_ty.clone());
                Ok(func_ty)
            }
            Expr::ResolvedVariable(depth) => {
                let ty = &env.type_stack[env.type_stack.len() - 1 - *depth as usize];
                env.types.insert(id, ty.clone());
                Ok(ty.clone())
            }
            Expr::Parameter(_) => todo!(
                "unresolved parameter: {:?}",
                self.parse_tree.get(id).unwrap()
            ),
            Expr::Variable(_) => todo!(
                "unresolved variable: {:?}",
                self.parse_tree.get(id).unwrap()
            ),
            Expr::Tuple(_) => todo!(),
            Expr::Unary(_token_kind, _) => todo!(),
            Expr::Binary(_, _token_kind, _) => todo!(),
            Expr::Block(items) => {
                for item in items {
                    self.infer_node(*item, env)?;
                }

                let return_ty = if let Some(last_id) = items.last() {
                    env.types.get(last_id).unwrap().clone()
                } else {
                    Ty::Void
                };

                env.types.insert(id, return_ty.clone());
                Ok(return_ty)
            }
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
        checker.infer().unwrap();
        checker.resolve().expect("did not resolve");
        checker
    }

    #[test]
    fn checks_an_int() {
        let checker = check("123");
        assert_eq!(checker.type_for(0).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_a_float() {
        let checker = check("123.");
        assert_eq!(checker.type_for(0).unwrap(), Ty::Float);
    }

    #[test]
    fn checks_a_func() {
        let checker = check("func sup(name) { name }\nsup");
        let root_id = checker.parse_tree.root_ids()[0];

        let Some(Ty::Func(params, return_type)) = checker.type_for(root_id) else {
            panic!("didnt get a func, got: {:#?}", checker.type_for(root_id));
        };

        let param_type = params[0].clone();

        assert_eq!(return_type, param_type.into());
        assert_eq!(return_type, Ty::TypeVar(TypeVarID(1)).into());

        assert_eq!(
            checker.type_for(checker.parse_tree.root_ids()[1]),
            Some(Ty::Func(params, return_type))
        );
    }

    #[test]
    fn checks_call() {
        let checker = check(
            "
        func fizz(c) { c }
        fizz(123)
        ",
        );

        let root_id = checker.parse_tree.root_ids()[1];
        assert_eq!(checker.type_for(root_id), Some(Ty::Int));
    }

    #[test]
    fn checks_a_let_assignment() {
        let checker = check("let count = 123\ncount");
        let root_id = checker.parse_tree.root_ids()[1];
        assert_eq!(checker.type_for(root_id), Some(Ty::Int));
    }
}
