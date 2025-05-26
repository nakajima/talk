use crate::{
    NameResolved, SymbolID, Typed,
    expr::{Expr, FuncName, Name},
    parser::ExprID,
    source_file::SourceFile,
};

use super::{
    builtins::match_builtin, constraint_solver::Constraint, environment::Environment,
    typed_expr::TypedExpr,
};

pub type FuncParams = Vec<Ty>;
pub type FuncReturning = Box<Ty>;

#[derive(Clone, PartialEq, Debug, Eq, Hash)]
pub struct TypeVarID(pub u32, pub TypeVarKind);

#[derive(Clone, PartialEq, Debug, Eq, Hash)]
pub enum TypeVarKind {
    Blank,
    CallArg,
    CallReturn,
    FuncParam,
    FuncNameVar(SymbolID),
    FuncBody,
    Let,
    TypeRepr(String),
}

#[derive(Debug, Clone, Copy)]
pub enum TypeError {}

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    Void,
    Int,
    Bool,
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

#[derive(Default, Debug)]
pub struct TypeChecker;

impl TypeChecker {
    pub fn infer(
        &self,
        source_file: SourceFile<NameResolved>,
    ) -> Result<(SourceFile<Typed>, Vec<Constraint>), TypeError> {
        let root_ids = source_file.root_ids();
        // Use a raw pointer to the source_file to avoid borrow checker issues
        let mut env = Environment::new();

        self.hoist_functions(&root_ids, &mut env, &source_file);

        let mut typed_roots = vec![];
        for id in root_ids {
            typed_roots.push(self.infer_node(id, &mut env, &None, &source_file)?)
        }

        let types = env.types;
        let constraints = env.constraints;

        // Now it's safe to move source_file since env is dropped before this line
        Ok((source_file.to_typed(typed_roots, types), constraints))
    }

    pub fn infer_node(
        &self,
        id: ExprID,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
        let expr = source_file.get(id).unwrap().clone();

        let result = match &expr {
            Expr::LiteralTrue | Expr::LiteralFalse => todo!(),
            Expr::Loop(_, _) => todo!(),
            Expr::If(_, _, _) => todo!(),
            Expr::Call(callee, args) => {
                let ret_var = if let Some(expected) = expected {
                    expected.clone()
                } else {
                    // Avoid borrow checker issue by creating the type variable before any borrows
                    let call_return_var = env.new_type_variable(TypeVarKind::CallReturn);
                    Ty::TypeVar(call_return_var)
                };

                let mut arg_tys: Vec<Ty> = vec![];
                for arg in args {
                    let ty = self.infer_node(*arg, env, &None, source_file).unwrap().ty;
                    arg_tys.push(ty);
                }

                let expected_callee_ty = Ty::Func(arg_tys, Box::new(ret_var.clone()));
                let callee_ty = self.infer_node(*callee, env, &None, source_file)?;

                env.constraints.push(Constraint::Equality(
                    *callee,
                    expected_callee_ty,
                    callee_ty.clone().ty,
                ));

                let typed_expr = TypedExpr::new(expr, ret_var);
                env.types.insert(id, typed_expr.clone());

                Ok(typed_expr)
            }
            Expr::LiteralInt(_) => {
                let typed_expr = TypedExpr::new(expr, Ty::Int);
                env.types.insert(id, typed_expr.clone());
                Ok(typed_expr)
            }
            Expr::LiteralFloat(_) => {
                let typed_expr = TypedExpr::new(expr, Ty::Float);
                env.types.insert(id, typed_expr.clone());
                Ok(typed_expr)
            }
            Expr::Assignment(lhs, rhs) => {
                let lhs_ty = self.infer_node(*lhs, env, &None, source_file)?;
                let rhs_ty = self.infer_node(*rhs, env, &None, source_file)?;

                env.constraints
                    .push(Constraint::Equality(*lhs, lhs_ty.clone().ty, rhs_ty.ty));

                env.types.insert(id, lhs_ty.clone());

                Ok(lhs_ty)
            }
            Expr::TypeRepr(name, _) => {
                let name = name.clone();

                let ty = match_builtin(name.clone()).unwrap_or_else(|| {
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::TypeRepr(name)))
                });

                let typed_expr = TypedExpr {
                    expr: expr.clone(),
                    ty,
                };

                env.types.insert(id, typed_expr.clone());

                Ok(typed_expr)
            }
            Expr::Func(name, params, body, ret) => {
                let mut func_var = None;

                let expected_body_ty = if let Some(ret) = ret {
                    Some(self.infer_node(*ret, env, &None, source_file)?.ty)
                } else {
                    None
                };
                //     ret.as_ref().map(|repr| {
                //     self.infer_node(*repr, env, &None, source_file)
                //         .unwrap()
                //         .ty
                //         .clone()
                // });

                if let Some(FuncName::Resolved(symbol_id)) = name {
                    let type_var = env.new_type_variable(TypeVarKind::FuncNameVar(*symbol_id));
                    func_var = Some(type_var.clone());
                    let scheme = env.generalize(&Ty::TypeVar(type_var));
                    env.declare(*symbol_id, scheme);
                    log::debug!("Declared scheme for named func {:?}, {:?}", symbol_id, env);
                }

                env.start_scope();

                let mut param_vars: Vec<Ty> = vec![];
                for expr_opt in params.iter() {
                    let expr = source_file.get(*expr_opt).cloned();
                    if let Some(Expr::Variable(Name::Resolved(symbol_id), ty)) = expr {
                        let var_ty = if let Some(ty_id) = ty {
                            self.infer_node(ty_id, env, expected, source_file)?.ty
                        } else {
                            Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncParam))
                        };

                        // Parameters are monomorphic inside the function body
                        let scheme = Scheme::new(var_ty.clone(), vec![]);
                        env.declare(symbol_id, scheme);
                        param_vars.push(var_ty);
                    }
                }

                let body_ty = self.infer_node(*body, env, &expected_body_ty, source_file)?;

                env.end_scope();

                let func_ty = Ty::Func(param_vars.clone(), Box::new(body_ty.ty));
                let func_typed_expr = TypedExpr {
                    expr: expr.clone(),
                    ty: func_ty.clone(),
                };

                env.types.insert(id, func_typed_expr.clone());

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

                Ok(func_typed_expr)
            }
            Expr::Let(Name::Resolved(symbol_id), rhs) => {
                let rhs_ty = if let Some(rhs) = rhs {
                    self.infer_node(*rhs, env, &None, source_file)?.ty
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

                let typed_expr = TypedExpr::new(expr, rhs_ty);
                env.types.insert(id, typed_expr.clone());

                Ok(typed_expr)
            }
            Expr::Variable(Name::Resolved(symbol_id), _) => {
                let ty = env.instantiate_symbol(*symbol_id);
                let typed_expr = TypedExpr { expr, ty };

                env.types.insert(id, typed_expr.clone());
                Ok(typed_expr)
            }
            Expr::Parameter(_, _) => {
                todo!("unresolved parameter: {:?}", source_file.get(id).unwrap())
            }
            Expr::Tuple(_) => todo!(),
            Expr::Unary(_token_kind, _) => todo!(),
            Expr::Binary(_, _token_kind, _) => todo!(),
            Expr::Block(items) => {
                env.start_scope();

                self.hoist_functions(items, env, source_file);

                let return_ty: Ty = {
                    let mut return_ty: Ty = Ty::Void;

                    for (i, item) in items.iter().enumerate() {
                        if i == items.len() - 1 {
                            return_ty = self.infer_node(*item, env, expected, source_file)?.ty;
                        } else {
                            self.infer_node(*item, env, &None, source_file)?;
                        }
                    }

                    return_ty
                };

                let return_ty = if let Some(expected) = expected {
                    if return_ty != *expected {
                        env.constraints
                            .push(Constraint::Equality(id, return_ty, expected.clone()));
                    }

                    expected.clone()
                } else {
                    return_ty.clone()
                };

                let typed_expr = TypedExpr::new(expr.clone(), return_ty);
                env.types.insert(id, typed_expr.clone());

                env.end_scope();

                Ok(typed_expr)
            }
            Expr::EnumDecl(_, _items1) => todo!(),
            Expr::EnumVariant(_, _items) => todo!(),
            Expr::Match(_, _items) => todo!(),
            Expr::MatchArm(_, _) => todo!(),
            Expr::PatternVariant(_, _, _items) => todo!(),
            Expr::MemberAccess(_, _) => todo!(),
            _ => panic!("Unhandled expr in type checker: {:?}", expr),
        };

        assert!(
            env.types.contains_key(&id),
            "did not set type for {:?}",
            result
        );

        result
    }

    fn hoist_functions(
        &self,
        node_ids: &[ExprID],
        env: &mut Environment,
        source_file: &SourceFile<NameResolved>,
    ) {
        for item in node_ids.iter() {
            let expr = source_file.get(*item).unwrap().clone();

            if let Expr::Func(Some(FuncName::Resolved(symbol_id)), ref _params, _body, _ret) = expr
            {
                let fn_var =
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncNameVar(symbol_id)));

                let typed_expr = TypedExpr::new(expr, fn_var.clone());
                env.types.insert(*item, typed_expr);

                let scheme = env.generalize(&fn_var);
                env.declare(symbol_id, scheme);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        SourceFile, Typed,
        constraint_solver::ConstraintSolver,
        name_resolver::NameResolver,
        parser::parse,
        type_checker::{Ty, TypeVarID, TypeVarKind},
    };

    use super::TypeChecker;

    fn check(code: &'static str) -> SourceFile<Typed> {
        let parsed = parse(code).unwrap();
        let resolver = NameResolver::new();
        let resolved = resolver.resolve(parsed);
        let checker = TypeChecker;
        let (mut typed, constraints) = checker.infer(resolved).unwrap();
        let mut constraint_solver = ConstraintSolver::new(&mut typed, constraints);
        constraint_solver.solve().unwrap();
        typed
    }

    #[test]
    fn checks_an_int() {
        let checker = check("123");
        assert_eq!(checker.type_for(0), Ty::Int);
    }

    #[test]
    fn checks_a_float() {
        let checker = check("123.");
        assert_eq!(checker.type_for(0), Ty::Float);
    }

    #[test]
    fn checks_a_named_func() {
        let checker = check("func sup(name) { name }\nsup");
        let root_id = checker.root_ids()[0];

        let Ty::Func(params, return_type) = checker.type_for(root_id) else {
            panic!("didnt get a func, got: {:#?}", checker.type_for(root_id));
        };

        let param_type = params[0].clone();

        assert_eq!(return_type, param_type.into());
        assert_eq!(
            *return_type,
            Ty::TypeVar(TypeVarID(3, TypeVarKind::FuncParam))
        );

        // The second root-expr is the *use* of `sup`.
        let Ty::Func(params2, return_type2) = checker.type_for(checker.root_ids()[1]) else {
            panic!(
                "expected `sup` to be a function, got: {:?}",
                checker.type_for(checker.root_ids()[1])
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
        let root_id = checker.root_ids()[0];
        let Ty::Func(params, return_type) = checker.type_for(root_id) else {
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

        let root_id = checker.root_ids()[1];
        assert_eq!(checker.type_for(root_id), Ty::Int);
    }

    #[test]
    fn checks_a_let_assignment() {
        let checker = check("let count = 123\ncount");
        let root_id = checker.root_ids()[1];
        assert_eq!(checker.type_for(root_id), Ty::Int);
    }

    #[test]
    fn checks_apply_twice() {
        let checker = check(
            "
        func applyTwice(f, x) { f(f(x)) }
        applyTwice
        ",
        );
        let root_id = checker.root_ids()[0];
        let Ty::Func(params, return_type) = checker.type_for(root_id) else {
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
        let root_id = checker.root_ids()[0];
        let Ty::Func(params, return_type) = checker.type_for(root_id) else {
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
        let root_id = checker.root_ids()[0];
        let ty = checker.type_for(root_id);
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

        let root_id = checker.root_ids()[0];
        let ty = checker.type_for(root_id);
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

        assert_eq!(checker.type_for(checker.root_ids()[1]), Ty::Int);
        assert_eq!(checker.type_for(checker.root_ids()[2]), Ty::Float);
    }
}
