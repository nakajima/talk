use std::collections::{HashMap, HashSet};

use crate::{
    expr::{Expr, FuncName},
    parse_tree::ParseTree,
    parser::ExprID,
    token::Token,
    token_kind::TokenKind,
};

use super::{
    builtins::match_builtin,
    constraint_solver::{Constraint, ConstraintError, ConstraintSolver},
    symbol_table::{SymbolID, SymbolTable},
    typed_expr::TypedExpr,
};

pub type FuncParams = Vec<Ty>;
pub type FuncReturning = Box<Ty>;

#[derive(Clone, Copy, PartialEq, Debug, Eq, Hash)]
pub struct TypeVarID(u32, TypeVarKind);

#[derive(Clone, Copy, PartialEq, Debug, Eq, Hash)]
pub enum TypeVarKind {
    Blank,
    CallArg,
    CallReturn,
    FuncParam,
    FuncNameVar(&'static str),
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
pub struct Environment {
    pub types: HashMap<ExprID, Ty>,
    pub type_var_id: TypeVarID,
    pub constraints: Vec<Constraint>,
    pub symbol_table: SymbolTable,
    pub scopes: Vec<HashMap<SymbolID, Scheme>>,
}

#[allow(clippy::new_without_default)]
impl Environment {
    pub fn new() -> Self {
        Self {
            types: HashMap::new(),
            type_var_id: TypeVarID(0, TypeVarKind::Blank),
            constraints: vec![],
            symbol_table: Default::default(),
            scopes: vec![Default::default()],
        }
    }

    /// Look up the scheme for `sym`, then immediately instantiate it.
    pub fn instantiate_symbol(&mut self, symbol_id: SymbolID) -> Ty {
        let scheme = self
            .scopes
            .iter()
            .rev()
            .find_map(|frame| frame.get(&symbol_id).cloned())
            .unwrap_or_else(|| panic!("missing symbol {:?} in {:?}",
                symbol_id, self.scopes));
        self.instantiate(&scheme)
    }

    pub fn start_scope(&mut self) {
        self.scopes.push(Default::default());
    }

    /// Take a monotype `t` and produce a Scheme ∀αᵢ. t,
    /// quantifying exactly those vars not free elsewhere in the env.
    pub fn generalize(&self, t: &Ty) -> Scheme {
        let ftv_t = free_type_vars(t);
        let ftv_env = free_type_vars_in_env(&self.scopes);
        let unbound_vars: Vec<TypeVarID> = ftv_t.difference(&ftv_env).cloned().collect();

        Scheme {
            unbound_vars,
            ty: t.clone(),
        }
    }

    /// Instantiate a polymorphic scheme into a fresh monotype:
    /// for each α ∈ scheme.vars, generate β = new_type_variable(α.kind),
    /// and substitute α ↦ β throughout scheme.ty.
    pub fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        // 1) build a map old_var → fresh_var
        let mut var_map: HashMap<TypeVarID, TypeVarID> = HashMap::new();
        for &old in &scheme.unbound_vars {
            // preserve the original kind when making a fresh one
            let fresh = self.new_type_variable(old.1);
            var_map.insert(old, fresh);
        }
        // 2) walk the type, replacing each old with its fresh
        fn walk(ty: &Ty, map: &HashMap<TypeVarID, TypeVarID>) -> Ty {
            match ty {
                Ty::TypeVar(tv) => {
                    if let Some(&new_tv) = map.get(tv) {
                        Ty::TypeVar(new_tv)
                    } else {
                        Ty::TypeVar(*tv)
                    }
                }
                Ty::Func(params, ret) => {
                    let new_params = params.iter().map(|p| walk(p, map)).collect();
                    let new_ret = Box::new(walk(ret, map));
                    Ty::Func(new_params, new_ret)
                }
                Ty::Void | Ty::Int | Ty::Float => ty.clone(),
            }
        }
        walk(&scheme.ty, &var_map)
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }

    #[track_caller]
    fn new_type_variable(&mut self, kind: TypeVarKind) -> TypeVarID {
        self.type_var_id = TypeVarID(self.type_var_id.0 + 1, kind);

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::warn!(
                "new_type_variable {:?} from {}:{}",
                Ty::TypeVar(self.type_var_id),
                loc.file(),
                loc.line()
            );
        }

        self.type_var_id
    }
}

#[derive(Debug)]
pub struct TypeChecker {
    pub symbol_table: SymbolTable,
    pub parse_tree: ParseTree,
    pub environment: Option<Environment>,
}

impl TypeChecker {
    pub fn new(symbol_table: SymbolTable, parse_tree: ParseTree) -> Self {
        Self {
            symbol_table,
            parse_tree,
            environment: None,
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
        let mut env = Environment::new();

        // self.hoist_functions(&self.parse_tree.root_ids(), &mut env);

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

                env.constraints.push(Constraint::Equality(
                    *callee,
                    expected_callee_ty,
                    callee_ty.clone().ty,
                ));

                env.types.insert(id, ret_var.clone());

                log::error!("Call return_ty: {:?}, callee: {:?}", ret_var, callee_ty);

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

                if let Some(FuncName::Token(Token {
                    kind: TokenKind::Identifier(name),
                    ..
                })) = name
                {
                    func_var = Some(env.new_type_variable(TypeVarKind::FuncNameVar(name)));
                }

                env.start_scope();

                let mut param_vars: Vec<Ty> = vec![];
                for (_i, expr_opt) in params.iter().map(|id| (*id, self.parse_tree.get(*id))) {
                    if let Some(Expr::ResolvedVariable(_depth, ty)) = expr_opt {
                        let var_ty = if let Some(ty_id) = ty {
                            self.infer_node(*ty_id, env, expected)?.ty
                        } else {
                            Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncParam))
                        };

                        param_vars.push(var_ty)
                    }
                }

                let body_ty = self.infer_node(*body, env, &expected_body_ty)?;

                env.end_scope();

                let func_ty = Ty::Func(param_vars.clone(), FuncReturning::new(body_ty.ty));

                if let Some(func_var) = &func_var {
                    env.constraints.push(Constraint::Equality(
                        id,
                        Ty::TypeVar(*func_var),
                        func_ty.clone(),
                    ));
                }

                env.types.insert(id, func_ty.clone());

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

                env.scopes.last_mut().unwrap().insert(*symbol_id, scheme);

                Ok(TypedExpr::new(id, rhs_ty))
            }
            Expr::ResolvedVariable(symbol_id, _) => {
                log::trace!(
                    "ResolvedVariable id: {:?}, type stack: {:?}",
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
                // self.hoist_functions(items, env);

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
            env.types.get(&id).is_some(),
            "did not set type for {:?}",
            result
        );

        result
    }

    // /// Instantiate a scheme by freshening its quantified vars.
    // pub fn instantiate(&mut self, scheme: &Scheme) -> Ty {
    //     let mut inst_sub = Substitution::new();
    //     for &qvar in &scheme.vars {
    //         inst_sub.insert(qvar, self.new_type_var().into());
    //     }
    //     inst_sub.apply(&scheme.ty)
    // }

    // /// After inferring a monotype `t`, generalize it w.r.t. the *rest* of the env.
    // pub fn generalize(&self, t: Ty) -> Scheme {
    //     let ftv_t = free_type_vars(&t);
    //     let ftv_env = free_type_vars_in_env(&self.subs, &self.scopes);
    //     let vars = ftv_t.difference(&ftv_env).cloned().collect();
    //     Scheme { vars, ty: t }
    // }

    pub fn type_for(&self, node_id: ExprID) -> Option<Ty> {
        let Some(env) = &self.environment else {
            panic!("no inference performed");
        };

        env.types.get(&node_id).cloned()
    }

    // fn hoist_functions(&self, node_ids: &Vec<ExprID>, env: &mut Environment) {
    //     for &item in node_ids.iter() {
    //         if let Expr::Func(
    //             Some(Token {
    //                 kind: TokenKind::Identifier(name),
    //                 ..
    //             }),
    //             _params,
    //             _body,
    //             _ret,
    //         ) = self.parse_tree.get(item).unwrap()
    //         {
    //             let fn_var = env.new_type_variable(TypeVarKind::FuncNameVar(name));
    //             env.types.insert(item, fn_var.clone().into());
    //             env.type_stack.push(fn_var.into());
    //         }
    //     }
    // }
}

/// Collect all type-variables occurring free in a single monotype.
pub fn free_type_vars(ty: &Ty) -> HashSet<TypeVarID> {
    let mut s = HashSet::new();
    match ty {
        Ty::TypeVar(v) => {
            s.insert(*v);
        }
        Ty::Func(params, ret) => {
            for p in params {
                s.extend(free_type_vars(p));
            }
            s.extend(free_type_vars(ret));
        }
        // add more Ty variants here as you grow them:
        // Ty::Tuple(elems)  => for e in elems { s.extend(free_type_vars(e)); }
        // Ty::ADT(name, args) => for a in args { s.extend(free_type_vars(a)); }
        _ => {}
    }
    s
}

/// Collect all free type-vars in *every* in-scope Scheme,
/// *after* applying the current substitutions.  We exclude
/// each scheme’s own quantified vars.
pub fn free_type_vars_in_env(scopes: &Vec<HashMap<SymbolID, Scheme>>) -> HashSet<TypeVarID> {
    let mut s = HashSet::new();

    for frame in scopes.iter() {
        for scheme in frame.values() {
            // collect its free vars
            let mut ftv = free_type_vars(&scheme.ty);

            // remove those vars that the scheme already quantifies
            for q in &scheme.unbound_vars {
                ftv.remove(q);
            }

            // everything remaining really is free in the env
            s.extend(ftv);
        }
    }

    s
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
    fn checks_a_func() {
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

        assert_eq!(
            checker.type_for(checker.parse_tree.root_ids()[1]),
            Some(Ty::Func(params, return_type))
        );
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
                "expected compose to return a function, got {:?}",
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
        assert_eq!(
            *ret,
            Ty::TypeVar(TypeVarID(4, TypeVarKind::CallReturn))
        );
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
