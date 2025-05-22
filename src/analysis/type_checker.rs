use crate::{
    expr::{Expr, FuncName},
    parse_tree::ParseTree,
    parser::ExprID,
};

use super::{
    builtins::match_builtin,
    constraint_solver::{Constraint, ConstraintError, ConstraintSolver},
    environment::Environment,
    symbol_table::{SymbolID, SymbolTable},
    typed_expr::TypedExpr,
};

pub type FuncParams = Vec<Ty>;
pub type FuncReturning = Box<Ty>;

#[derive(Clone, Copy, PartialEq, Debug, Eq, Hash)]
pub struct TypeVarID(pub u32, pub TypeVarKind);

#[derive(Clone, Copy, PartialEq, Debug, Eq, Hash)]
pub enum TypeVarKind {
    Blank,
    CallArg,
    CallReturn,
    FuncParam,
    FuncNameVar(SymbolID),
    FuncBody,
    Let,
    TypeRepr(&'static str),
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

#[derive(Debug, Clone)]
pub struct Scheme {
    pub ty: Ty,
    pub unbound_vars: Vec<TypeVarID>,
}

impl Scheme {
    pub fn new(ty: Ty, unbound_vars: Vec<TypeVarID>) -> Self {
        Self { ty, unbound_vars }
    }
}

#[derive(Debug)]
pub struct TypeChecker {
    pub parse_tree: ParseTree,
    pub environment: Option<Environment>,
}

impl TypeChecker {
    pub fn new(symbol_table: SymbolTable, parse_tree: ParseTree) -> Self {
        Self {
            parse_tree,
            environment: Some(Environment::new(symbol_table)),
        }
    }

    pub fn define(&mut self, node_id: ExprID, ty: Ty) {
        self.environment
            .as_mut()
            .expect("type inference not performed")
            .types
            .insert(node_id, ty);
    }

    pub fn infer(&mut self) -> Result<Vec<TypedExpr>, TypeError> {
        let mut env = self.environment.take().unwrap();

        self.hoist_functions(&self.parse_tree.root_ids(), &mut env);

        let typed_roots = self
            .parse_tree
            .root_ids()
            .iter()
            .map(|id| self.infer_node(*id, &mut env, &None))
            .collect::<Result<Vec<_>, _>>()?;

        self.environment = Some(env);

        Ok(typed_roots)
    }

    pub fn resolve(&mut self) -> Result<(), ConstraintError> {
        let mut constraints = self.environment.as_ref().unwrap().constraints.clone();
        let mut resolver = ConstraintSolver::new(self, &mut constraints);

        resolver.solve()
    }

    pub fn infer_node(
        &self,
        id: ExprID,
        env: &mut Environment,
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        let result = match &self.parse_tree.get(id).unwrap() {
            Expr::Call(callee, args) => {
                let ret_var = if let Some(expected) = expected {
                    expected.clone()
                } else {
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::CallReturn))
                };

                let mut arg_tys: Vec<Ty> = vec![];
                for arg in args {
                    let ty = self.infer_node(*arg, env, &None).unwrap().ty;
                    arg_tys.push(ty);
                }

                let expected_callee_ty = Ty::Func(arg_tys, Box::new(ret_var.clone()));
                let callee_ty = self.infer_node(*callee, env, &None)?;

                log::debug!("callee: {:?}", callee);
                log::debug!("Expected callee_ty: {:?}", expected_callee_ty);
                log::debug!("callee_ty: {:?}", callee_ty);

                env.constraints.push(Constraint::Equality(
                    *callee,
                    expected_callee_ty,
                    callee_ty.clone().ty,
                ));

                env.types.insert(id, ret_var.clone());

                Ok(TypedExpr::new(id, ret_var))
            }
            Expr::LiteralInt(_) => {
                env.types.insert(id, Ty::Int);
                Ok(TypedExpr::new(id, Ty::Int))
            }
            Expr::LiteralFloat(_) => {
                env.types.insert(id, Ty::Float);
                Ok(TypedExpr::new(id, Ty::Float))
            }
            Expr::Assignment(lhs, rhs) => {
                let lhs_ty = self.infer_node(*lhs, env, &None)?;
                let rhs_ty = self.infer_node(*rhs, env, &None)?;

                env.constraints
                    .push(Constraint::Equality(*lhs, lhs_ty.ty.clone(), rhs_ty.ty));

                env.types.insert(id, lhs_ty.clone().ty);

                Ok(lhs_ty)
            }
            Expr::Let(_name, _) => {
                unreachable!("unresolved let found")
            }
            Expr::TypeRepr(name) => {
                let typed_expr = TypedExpr {
                    expr: id,
                    ty: (match_builtin(name).unwrap_or_else(|| {
                        Ty::TypeVar(env.new_type_variable(TypeVarKind::TypeRepr(name)))
                    })),
                };

                env.types.insert(id, typed_expr.clone().ty.clone());

                Ok(typed_expr)
            }
            Expr::Func(name, params, body, ret) => {
                let mut func_var = None;

                let expected_body_ty = ret
                    .as_ref()
                    .map(|repr| self.infer_node(*repr, env, &None).unwrap().ty);

                if let Some(FuncName::Resolved(symbol_id)) = name {
                    let type_var = env.new_type_variable(TypeVarKind::FuncNameVar(*symbol_id));
                    func_var = Some(type_var);
                    let scheme = env.generalize(&Ty::TypeVar(type_var));
                    env.declare(*symbol_id, scheme);
                    log::debug!("Declared scheme for named func {:?}, {:?}", symbol_id, env);
                }

                env.start_scope();

                let mut param_vars: Vec<Ty> = vec![];
                for expr_opt in params.iter().filter_map(|id| self.parse_tree.get(*id)) {
                    if let Expr::ResolvedVariable(symbol_id, ty) = expr_opt {
                        let var_ty = if let Some(ty_id) = ty {
                            self.infer_node(*ty_id, env, expected)?.ty
                        } else {
                            Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncParam))
                        };

                        // Parameters are monomorphic inside the function body
                        let scheme = Scheme::new(var_ty.clone(), vec![]);
                        env.declare(*symbol_id, scheme);
                        param_vars.push(var_ty);
                    }
                }

                let body_ty = self.infer_node(*body, env, &expected_body_ty)?;

                env.end_scope();

                let func_ty = Ty::Func(param_vars.clone(), FuncReturning::new(body_ty.ty));

                env.types.insert(id, func_ty.clone());

                if let Some(func_var) = func_var {
                    env.constraints.push(Constraint::Equality(
                        id,
                        Ty::TypeVar(func_var),
                        func_ty.clone(),
                    ));

                    if let Some(FuncName::Resolved(symbol_id)) = name {
                        let scheme = if env.scopes.len() > 1 {
                            Scheme::new(func_ty.clone(), vec![])
                        } else {
                            env.generalize(&func_ty)
                        };
                        env.scopes.last_mut().unwrap().insert(*symbol_id, scheme);
                    }
                }

                Ok(TypedExpr::new(id, func_ty))
            }
            Expr::ResolvedLet(symbol_id, rhs) => {
                let rhs_ty = if let Some(rhs) = rhs {
                    self.infer_node(*rhs, env, &None)?.ty
                } else {
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::Let))
                };

                let scheme = if rhs.is_some() {
                    env.generalize(&rhs_ty)
                } else {
                    // no init ⇒ treat as a single hole, not a forall
                    Scheme {
                        unbound_vars: vec![],
                        ty: rhs_ty.clone(),
                    }
                };

                env.scopes
                    .last_mut()
                    .unwrap()
                    .insert(*symbol_id, scheme.clone());

                env.types.insert(id, scheme.ty);

                Ok(TypedExpr::new(id, rhs_ty))
            }
            Expr::ResolvedVariable(symbol_id, _) => {
                log::trace!(
                    "ResolvedVariable id: {:?}, symbol table: {:?}",
                    symbol_id,
                    env.symbol_table
                );

                let ty = env.instantiate_symbol(*symbol_id);

                env.types.insert(id, ty.clone());
                Ok(TypedExpr { expr: id, ty })
            }
            Expr::Parameter(_, _) => todo!(
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
                self.hoist_functions(items, env);

                let return_ty: Ty = {
                    let mut return_ty: Ty = Ty::Void;

                    for (i, item) in items.iter().enumerate() {
                        if i == items.len() - 1 {
                            return_ty = self.infer_node(*item, env, expected)?.ty;
                        } else {
                            self.infer_node(*item, env, &None)?;
                        }
                    }

                    return_ty
                };

                let return_ty = if let Some(expected) = expected {
                    if &return_ty != expected {
                        env.constraints.push(Constraint::Equality(
                            id,
                            return_ty.clone(),
                            expected.clone(),
                        ));
                    }

                    expected.clone()
                } else {
                    return_ty.clone()
                };

                env.types.insert(id, return_ty.clone());

                Ok(TypedExpr::new(id, return_ty))
            }
        };

        assert!(
            env.types.contains_key(&id),
            "did not set type for {:?}",
            result
        );

        result
    }

    pub fn type_for(&self, node_id: ExprID) -> Option<Ty> {
        let Some(env) = &self.environment else {
            panic!("no inference performed");
        };

        env.types.get(&node_id).cloned()
    }

    fn hoist_functions(&self, node_ids: &[ExprID], env: &mut Environment) {
        for &item in node_ids.iter() {
            if let Expr::Func(Some(FuncName::Resolved(symbol_id)), _params, _body, _ret) =
                self.parse_tree.get(item).unwrap()
            {
                let fn_var =
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncNameVar(*symbol_id)));
                env.types.insert(item, fn_var.clone());

                let scheme = env.generalize(&fn_var);
                env.declare(*symbol_id, scheme);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        name_resolver::NameResolver,
        parser::parse,
        type_checker::{Ty, TypeVarID, TypeVarKind},
    };

    use super::TypeChecker;

    fn check(code: &'static str) -> TypeChecker {
        let mut parsed = parse(code).unwrap();
        let resolver = NameResolver::new();
        let (symbol_table, resolved) = resolver.resolve(&mut parsed);
        let mut checker = TypeChecker::new(symbol_table, resolved.clone());
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
    fn checks_a_named_func() {
        let checker = check("func sup(name) { name }\nsup");
        let root_id = checker.parse_tree.root_ids()[0];

        let Some(Ty::Func(params, return_type)) = checker.type_for(root_id) else {
            panic!("didnt get a func, got: {:#?}", checker.type_for(root_id));
        };

        let param_type = params[0].clone();

        assert_eq!(return_type, param_type.into());
        assert_eq!(
            *return_type,
            Ty::TypeVar(TypeVarID(3, TypeVarKind::FuncParam))
        );

        // The second root-expr is the *use* of `sup`.
        let Some(Ty::Func(params2, return_type2)) =
            checker.type_for(checker.parse_tree.root_ids()[1])
        else {
            panic!(
                "expected `sup` to be a function, got: {:?}",
                checker.type_for(checker.parse_tree.root_ids()[1])
            );
        };

        // It must still be a one-parameter function …
        assert_eq!(params2.len(), 1);
        // … whose return type equals its parameter (α → α),
        // even though this α is a fresh type-variable distinct
        // from the one in the definition above.
        assert_eq!(*return_type2, params2[0].clone());
    }

    #[test]
    fn checks_a_func_with_return_type() {
        let checker = check("func sup(name) -> Int { name }\n");
        let root_id = checker.parse_tree.root_ids()[0];
        let Some(Ty::Func(params, return_type)) = checker.type_for(root_id) else {
            panic!("didnt get a func, got: {:#?}", checker.type_for(root_id));
        };

        assert_eq!(params, vec![Ty::Int]);
        assert_eq!(*return_type, Ty::Int);
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

    #[test]
    fn checks_apply_twice() {
        let checker = check(
            "
        func applyTwice(f, x) { f(f(x)) }
        applyTwice
        ",
        );
        let root_id = checker.parse_tree.root_ids()[0];
        let Some(Ty::Func(params, return_type)) = checker.type_for(root_id) else {
            panic!(
                "expected `applyTwice` to be a function, got: {:?}",
                checker.type_for(root_id)
            );
        };

        // applyTwice should have exactly 2 parameters
        assert_eq!(params.len(), 2);

        // f : A -> A
        match &params[0] {
            Ty::Func(arg_tys, ret_ty) => {
                assert_eq!(arg_tys.len(), 1);
                // the return of f must be the same type as x
                assert_eq!(**ret_ty, params[1].clone());
            }
            other => panic!("`f` should be a function, got {:?}", other),
        }

        // the overall return type of applyTwice is the same as x
        assert_eq!(return_type, params[1].clone().into());
    }

    #[test]
    fn checks_composition() {
        let checker = check(
            "
        func compose(f, g) {
            func inner(x) { f(g(x)) }
            inner
        }
        compose
        ",
        );
        let root_id = checker.parse_tree.root_ids()[0];
        let Some(Ty::Func(params, return_type)) = checker.type_for(root_id) else {
            panic!(
                "expected `compose` to be a function, got: {:?}",
                checker.type_for(root_id)
            );
        };

        // compose should have exactly 2 parameters: f and g
        assert_eq!(params.len(), 2);
        let f_ty = &params[0];
        let g_ty = &params[1];

        // f : B -> C
        let Ty::Func(f_args, f_ret) = f_ty.clone() else {
            panic!("did not get func: {:?}", f_ty);
        };
        assert_eq!(f_args.len(), 1);

        // g : A -> B
        let Ty::Func(g_args, g_ret) = g_ty.clone() else {
            panic!("did not get func")
        };

        assert_eq!(g_args.len(), 1);

        // g’s return type (B) must match f’s argument type
        assert_eq!(*g_ret, f_args[0].clone());

        // the inner function’s return (and thus compose’s return) is f’s return type C
        let Ty::Func(inner_params, inner_ret) = *return_type else {
            panic!(
                "expected `compose` to return a function, got {:?}",
                return_type
            );
        };
        assert_eq!(inner_params.len(), 1);
        assert_eq!(inner_params[0], g_args[0].clone()); // inner’s x : A
        assert_eq!(*inner_ret, *f_ret.clone()); // inner returns C
    }

    #[test]
    fn checks_simple_recursion() {
        let checker = check(
            "
        func rec(n) {
            rec(n)
        }
        rec
        ",
        );

        // the bare `rec` at the top level should be a Func([α], α)
        let root_id = checker.parse_tree.root_ids()[0];
        let ty = checker.type_for(root_id).unwrap();
        let Ty::Func(params, ret) = ty else { panic!() };
        // exactly one parameter
        assert_eq!(params.len(), 1);
        // return type equals the parameter type
        assert_eq!(*ret, Ty::TypeVar(TypeVarID(4, TypeVarKind::CallReturn)));
    }

    #[test]
    fn checks_mutual_recursion() {
        let checker = check(
            "
        func even(n: Int) -> Int {
            odd(n)
        }
        func odd(n: Int) -> Int {
            even(n)
        }
        even
        ",
        );

        let root_id = checker.parse_tree.root_ids()[0];
        let ty = checker.type_for(root_id).unwrap();
        match ty {
            Ty::Func(params, ret) => {
                assert_eq!(params.len(), 1);
                // both even and odd must have the same input and output type
                assert_eq!(*ret, Ty::Int);
                assert_eq!(params[0].clone(), Ty::Int);
            }
            other => panic!("expected a function, got {:?}", other),
        }
    }

    #[test]
    fn infers_identity() {
        let checker = check(
            "
            func identity(arg) { arg }
            identity(1)
            identity(2.0)
        ",
        );

        assert_eq!(
            checker.type_for(checker.parse_tree.root_ids()[1]).unwrap(),
            Ty::Int
        );
        assert_eq!(
            checker.type_for(checker.parse_tree.root_ids()[2]).unwrap(),
            Ty::Float
        );
    }
}
