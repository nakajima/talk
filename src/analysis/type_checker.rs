use std::collections::HashMap;

use crate::{
    NameResolved, SymbolID, Typed,
    environment::{EnumVariant, free_type_vars},
    expr::{Expr, FuncName, Pattern},
    match_builtin,
    name::Name,
    parser::ExprID,
    prelude::PRELUDE,
    source_file::SourceFile,
};

use super::{
    constraint_solver::Constraint,
    environment::{EnumDef, Environment, TypeDef},
    typed_expr::TypedExpr,
};

pub type TypeDefs = HashMap<SymbolID, TypeDef>;
pub type FuncParams = Vec<Ty>;
pub type FuncReturning = Box<Ty>;

#[derive(Clone, PartialEq, Debug, Eq, Hash)]
pub struct TypeVarID(pub i32, pub TypeVarKind);

#[derive(Clone, PartialEq, Debug, Eq, Hash)]
pub enum TypeVarKind {
    Blank,
    CallArg,
    CallReturn,
    FuncParam,
    FuncType,
    FuncNameVar(SymbolID),
    FuncBody,
    Let,
    TypeRepr(Name),
    Member,
    VariantValue,
    PatternBind(Name),
}

#[derive(Debug, Clone)]
pub enum TypeError {
    Unresolved,
    InvalidEnumAccess,
    UnknownEnum(SymbolID),
    UnknownVariant(Name),
    Unknown(&'static str),
}

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
    Enum(SymbolID, Vec<Ty>), // enum name + type arguments
    EnumVariant(SymbolID /* Enum */, Vec<Ty> /* Values */),
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
    ) -> Result<SourceFile<Typed>, TypeError> {
        let mut env = Environment::new();

        // Just import the prelude
        env.import_prelude(&PRELUDE.types, &PRELUDE.schemes);

        self.infer_without_prelude(env, source_file)
    }

    pub fn infer_without_prelude(
        &self,
        mut env: Environment,
        mut source_file: SourceFile<NameResolved>,
    ) -> Result<SourceFile<Typed>, TypeError> {
        let root_ids = source_file.root_ids();

        self.hoist_enums(&root_ids, &mut env, &mut source_file)?;
        self.hoist_functions(&root_ids, &mut env, &source_file);

        let mut typed_roots = vec![];
        for id in root_ids {
            typed_roots.push(self.infer_node(id, &mut env, &None, &source_file)?)
        }

        // Now it's safe to move source_file since env is dropped before this line
        Ok(source_file.to_typed(typed_roots, env))
    }

    pub fn infer_node(
        &self,
        id: ExprID,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
        let expr = source_file.get(id).unwrap().clone();
        log::trace!("Inferring {:?}", expr);

        let result = match &expr {
            Expr::LiteralTrue | Expr::LiteralFalse => self.infer_literal_bool(id, env, expr),
            Expr::Loop(_, _) => self.infer_loop(id, env, expr),
            Expr::If(_, _, _) => self.infer_if(id, env, expr),
            Expr::Call(callee, args) => {
                self.infer_call(id, env, expr.clone(), *callee, args, expected, source_file)
            }
            Expr::LiteralInt(_) => self.infer_literal_int(id, env, expr),
            Expr::LiteralFloat(_) => self.infer_literal_float(id, env, expr),
            Expr::Assignment(lhs, rhs) => {
                self.infer_assignment(id, env, expr.clone(), *lhs, *rhs, source_file)
            }
            Expr::TypeRepr(name, generics, is_type_parameter) => self.infer_type_repr(
                id,
                env,
                expr.clone(),
                name,
                generics,
                *is_type_parameter,
                source_file,
            ),
            Expr::FuncTypeRepr(args, ret, _is_type_parameter) => {
                self.infer_func_type_repr(id, env, expr.clone(), args, *ret, expected, source_file)
            }
            Expr::Func(name, generics, params, body, ret) => self.infer_func(
                id,
                env,
                expr.clone(),
                name,
                generics,
                params,
                *body,
                ret,
                expected,
                source_file,
            ),
            Expr::Let(Name::Resolved(symbol_id, _), rhs) => {
                self.infer_let(id, env, expr.clone(), *symbol_id, rhs, source_file)
            }
            Expr::Variable(Name::Resolved(symbol_id, name), _) => {
                self.infer_variable(id, env, expr.clone(), *symbol_id, name)
            }
            Expr::Parameter(_, _) => {
                panic!("unresolved parameter: {:?}", source_file.get(id).unwrap())
            }
            Expr::Tuple(_) => self.infer_tuple(id, env, expr),
            Expr::Unary(_token_kind, _) => self.infer_unary(id, env, expr),
            Expr::Binary(_lhs, _token_kind, _rhs) => self.infer_binary(id, env, expr),
            Expr::Block(items) => {
                self.infer_block(id, env, expr.clone(), items, expected, source_file)
            }
            Expr::EnumDecl(_, _generics, _body) => Ok(env.typed_exprs.get(&id).unwrap().clone()),
            Expr::EnumVariant(_, _) => Ok(env.typed_exprs.get(&id).unwrap().clone()),
            Expr::Match(pattern, items) => {
                self.infer_match(id, env, expr.clone(), *pattern, items, source_file)
            }
            Expr::MatchArm(pattern, body) => self.infer_match_arm(
                id,
                env,
                expr.clone(),
                *pattern,
                *body,
                expected,
                source_file,
            ),
            Expr::PatternVariant(_, _, _items) => self.infer_pattern_variant(id, env, expr),
            Expr::Member(receiver, member_name) => {
                self.infer_member(id, env, expr.clone(), receiver, member_name, source_file)
            }
            Expr::Pattern(pattern) => {
                self.infer_pattern_expr(id, env, expr.clone(), pattern, expected)
            }
            Expr::Variable(Name::Raw(_), _) => Err(TypeError::Unresolved),
            _ => panic!("Unhandled expr in type checker: {:?}", expr),
        };

        assert!(
            env.typed_exprs.contains_key(&id),
            "did not set type for {:?}",
            result
        );

        result
    }

    fn infer_literal_bool(
        &self,
        _id: ExprID,
        _env: &mut Environment,
        _expr: Expr,
    ) -> Result<TypedExpr, TypeError> {
        todo!()
    }

    fn infer_loop(
        &self,
        _id: ExprID,
        _env: &mut Environment,
        _expr: Expr,
    ) -> Result<TypedExpr, TypeError> {
        todo!()
    }

    fn infer_if(
        &self,
        _id: ExprID,
        _env: &mut Environment,
        _expr: Expr,
    ) -> Result<TypedExpr, TypeError> {
        todo!()
    }

    fn infer_call(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        callee: ExprID,
        args: &[ExprID],
        expected: &Option<Ty>,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
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
        let callee_ty = self.infer_node(callee, env, &None, source_file)?;

        env.constraints.push(Constraint::Equality(
            callee,
            expected_callee_ty,
            callee_ty.clone().ty,
        ));

        let typed_expr = TypedExpr::new(expr, ret_var);
        env.typed_exprs.insert(id, typed_expr.clone());

        Ok(typed_expr)
    }

    fn infer_literal_int(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
    ) -> Result<TypedExpr, TypeError> {
        let typed_expr = TypedExpr::new(expr, Ty::Int);
        env.typed_exprs.insert(id, typed_expr.clone());
        Ok(typed_expr)
    }

    fn infer_literal_float(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
    ) -> Result<TypedExpr, TypeError> {
        let typed_expr = TypedExpr::new(expr, Ty::Float);
        env.typed_exprs.insert(id, typed_expr.clone());
        Ok(typed_expr)
    }

    fn infer_assignment(
        &self,
        id: ExprID,
        env: &mut Environment,
        _expr: Expr,
        lhs: ExprID,
        rhs: ExprID,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
        let lhs_ty = self.infer_node(lhs, env, &None, source_file)?;
        let rhs_ty = self.infer_node(rhs, env, &None, source_file)?;

        env.constraints
            .push(Constraint::Equality(lhs, lhs_ty.clone().ty, rhs_ty.ty));

        env.typed_exprs.insert(id, lhs_ty.clone());

        Ok(lhs_ty)
    }

    fn infer_type_repr(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        name: &Name,
        generics: &[ExprID],
        is_type_parameter: bool,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
        let name = name.clone();
        log::debug!(
            "TYPE REPR: {:?}, is_param_decl: {}",
            name,
            is_type_parameter
        );

        let ty = match &name {
            Name::Raw(raw_name) => {
                if let Some(builtin_ty) = match_builtin(&Name::Raw(raw_name.clone())) {
                    builtin_ty
                } else {
                    // Raw name that is not a builtin.
                    // If it's a type parameter declaration, create a new type variable.
                    // Otherwise, it's an unresolved type name (error) or needs other handling.
                    // For now, to allow forward enum declarations, we might make it a TypeVar.
                    // This part might need more robust error handling for unknown types.
                    if is_type_parameter {
                        Ty::TypeVar(env.new_type_variable(TypeVarKind::TypeRepr(name.clone())))
                    } else {
                        // Attempting to use an unresolved raw name as a type.
                        // This should ideally be an error or a placeholder needing resolution.
                        // For now, create a type variable, similar to previous behavior.
                        log::warn!(
                            "Encountered unresolved raw type name in usage: {:?}",
                            raw_name
                        );
                        Ty::TypeVar(env.new_type_variable(TypeVarKind::TypeRepr(name.clone())))
                    }
                }
            }
            Name::Resolved(symbol_id, _name_str) => {
                if is_type_parameter {
                    // Declaration site of a type parameter (e.g., T in `enum Option<T>`).
                    // Create a new type variable for it.
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::TypeRepr(name.clone())))
                } else {
                    // Usage of a resolved type name (e.g., T in `case some(T)` or `Int`).
                    // Instantiate its scheme from the environment.
                    env.instantiate_symbol(*symbol_id)
                }
            }
        };

        // For generic types like Option<Int>, we need to handle the generics
        if !generics.is_empty() && !is_type_parameter {
            // First, infer all the generic arguments
            let mut generic_types = Vec::new();
            for generic_id in generics {
                let generic_ty = self.infer_node(*generic_id, env, &None, source_file)?.ty;
                generic_types.push(generic_ty);
            }

            // Now when we have a resolved symbol for a generic type
            if let Name::Resolved(symbol_id, _) = name {
                // Instead of just instantiating, we need to build the concrete type
                // For enums, this means Ty::Enum(symbol_id, generic_types)
                let ty = Ty::Enum(symbol_id, generic_types);

                let typed_expr = TypedExpr {
                    expr: expr.clone(),
                    ty,
                };
                env.typed_exprs.insert(id, typed_expr.clone());
                return Ok(typed_expr);
            }
        }

        if is_type_parameter {
            // This is for the T in `enum Option<T>`. Name should be resolved by name_resolver.
            let Name::Resolved(symbol_id, _) = name else {
                panic!(
                    "Type parameter name {:?} was not resolved during its declaration",
                    name
                )
            };
            log::debug!(
                "Declaring type parameter {:?} ({:?}) with ty {:?}",
                symbol_id,
                name,
                ty
            );
            // Type parameters are monomorphic within their defining generic scope.
            // So, references to this type parameter within this scope refer to this 'ty'.
            env.declare(symbol_id, Scheme::new(ty.clone(), vec![]));
        }

        let typed_expr = TypedExpr {
            expr: expr.clone(),
            ty,
        };

        env.typed_exprs.insert(id, typed_expr.clone());

        Ok(typed_expr)
    }

    fn infer_func_type_repr(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        args: &[ExprID],
        ret: ExprID,
        expected: &Option<Ty>,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
        let mut inferred_args = vec![];
        for arg in args {
            inferred_args.push(self.infer_node(*arg, env, expected, source_file)?.ty);
        }

        let inferred_ret = self.infer_node(ret, env, expected, source_file)?.ty;

        let ty = Ty::Func(inferred_args, Box::new(inferred_ret));

        let typed_expr = TypedExpr {
            expr: expr.clone(),
            ty,
        };

        env.typed_exprs.insert(id, typed_expr.clone());

        Ok(typed_expr)
    }

    fn infer_func(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        name: &Option<FuncName>,
        generics: &[ExprID],
        params: &[ExprID],
        body: ExprID,
        ret: &Option<ExprID>,
        expected: &Option<Ty>,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
        let mut func_var = None;

        if let Some(FuncName::Resolved(symbol_id)) = name {
            let type_var = env.new_type_variable(TypeVarKind::FuncNameVar(*symbol_id));
            func_var = Some(type_var.clone());
            let scheme = env.generalize(&Ty::TypeVar(type_var));
            env.declare(*symbol_id, scheme);
            log::debug!("Declared scheme for named func {:?}, {:?}", symbol_id, env);
        }

        env.start_scope();

        // Infer generic type parameters
        let mut generic_vars = vec![];
        for generic_id in generics {
            let ty = self.infer_node(*generic_id, env, &None, source_file)?.ty;
            generic_vars.push(ty);

            // If this is a type parameter declaration, we need to declare it in the environment
            if let Expr::TypeRepr(Name::Resolved(symbol_id, _), _, true) =
                source_file.get(*generic_id).unwrap()
            {
                // The type was already created by infer_node, so we just need to get it
                if let Some(typed_expr) = env.typed_exprs.get(generic_id) {
                    env.declare(*symbol_id, Scheme::new(typed_expr.ty.clone(), vec![]));
                }
            }
        }

        let expected_body_ty = if let Some(ret) = ret {
            Some(self.infer_node(*ret, env, &None, source_file)?.ty)
        } else {
            None
        };

        let ret_type_expr: Option<TypedExpr> = ret
            .as_ref()
            .map(|repr| self.infer_node(*repr, env, &None, source_file))
            .transpose()
            .unwrap_or(None);

        let mut param_vars: Vec<Ty> = vec![];
        for expr_opt in params.iter() {
            let expr = source_file.get(*expr_opt).cloned();
            if let Some(Expr::Variable(Name::Resolved(symbol_id, _), ty)) = expr {
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

        let body_ty = self.infer_node(body, env, &expected_body_ty, source_file)?;

        if let Some(ret_type) = ret_type_expr {
            env.constraints.push(Constraint::Equality(
                ret.unwrap(),
                body_ty.ty.clone(),
                ret_type.ty,
            ));
        }

        env.end_scope();

        let func_ty = Ty::Func(param_vars.clone(), Box::new(body_ty.ty));
        let func_typed_expr = TypedExpr {
            expr: expr.clone(),
            ty: func_ty.clone(),
        };

        env.typed_exprs.insert(id, func_typed_expr.clone());

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

    fn infer_let(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        symbol_id: SymbolID,
        rhs: &Option<ExprID>,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
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
            .insert(symbol_id, scheme.clone());

        let typed_expr = TypedExpr::new(expr, rhs_ty);
        env.typed_exprs.insert(id, typed_expr.clone());

        Ok(typed_expr)
    }

    fn infer_variable(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        symbol_id: SymbolID,
        name: &str,
    ) -> Result<TypedExpr, TypeError> {
        let ty = env.instantiate_symbol(symbol_id);
        log::trace!("instantiated {:?} ({:?}) with {:?}", symbol_id, name, ty);
        let typed_expr = TypedExpr { expr, ty };

        env.typed_exprs.insert(id, typed_expr.clone());
        Ok(typed_expr)
    }

    fn infer_tuple(
        &self,
        _id: ExprID,
        _env: &mut Environment,
        _expr: Expr,
    ) -> Result<TypedExpr, TypeError> {
        todo!()
    }

    fn infer_unary(
        &self,
        _id: ExprID,
        _env: &mut Environment,
        _expr: Expr,
    ) -> Result<TypedExpr, TypeError> {
        todo!()
    }

    fn infer_binary(
        &self,
        _id: ExprID,
        _env: &mut Environment,
        _expr: Expr,
    ) -> Result<TypedExpr, TypeError> {
        todo!()
    }

    fn infer_block(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        items: &[ExprID],
        expected: &Option<Ty>,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
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
        env.typed_exprs.insert(id, typed_expr.clone());

        env.end_scope();

        Ok(typed_expr)
    }

    fn infer_match(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        pattern: ExprID,
        items: &[ExprID],
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
        let pattern_ty = self.infer_node(pattern, env, &None, source_file)?.ty;
        let items_ty = items
            .iter()
            .map(|id| self.infer_node(*id, env, &Some(pattern_ty.clone()), source_file))
            .collect::<Result<Vec<_>, _>>()?;
        let items_ty = items_ty.iter().map(|ty| ty.ty.clone()).collect::<Vec<_>>();

        // TODO: Make sure the return type is the same for all arms
        let ret_ty = items_ty.last().unwrap().clone();

        let typed_expr = TypedExpr::new(expr, ret_ty);
        env.typed_exprs.insert(id, typed_expr.clone());
        Ok(typed_expr)
    }

    fn infer_match_arm(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        pattern: ExprID,
        body: ExprID,
        expected: &Option<Ty>,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
        env.start_scope();
        let _pattern_ty = self.infer_node(pattern, env, expected, source_file)?.ty;
        let body_ty = self.infer_node(body, env, &None, source_file)?.ty;
        env.end_scope();

        let typed_expr = TypedExpr::new(expr, body_ty);
        env.typed_exprs.insert(id, typed_expr.clone());
        Ok(typed_expr)
    }

    fn infer_pattern_variant(
        &self,
        _id: ExprID,
        _env: &mut Environment,
        _expr: Expr,
    ) -> Result<TypedExpr, TypeError> {
        todo!()
    }

    fn infer_member(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        receiver: &Option<ExprID>,
        member_name: &str,
        source_file: &SourceFile<NameResolved>,
    ) -> Result<TypedExpr, TypeError> {
        match receiver {
            None => {
                // Unqualified: .some
                // Create a type variable that will be constrained later
                let member_var = env.new_type_variable(TypeVarKind::Member);

                env.constraints.push(Constraint::UnqualifiedMember(
                    id,
                    member_name.to_string(),
                    Ty::TypeVar(member_var.clone()),
                ));

                let typed_expr = TypedExpr::new(expr, Ty::TypeVar(member_var));

                env.typed_exprs.insert(id, typed_expr.clone());
                Ok(typed_expr)
            }
            Some(receiver_id) => {
                // Qualified: Option.some
                let receiver_ty = self.infer_node(*receiver_id, env, &None, source_file)?;

                // Create a type variable for the member
                let member_var = env.new_type_variable(TypeVarKind::Member);

                // Add a constraint that links the receiver type to the member
                env.constraints.push(Constraint::MemberAccess(
                    id,
                    receiver_ty.ty,
                    member_name.to_string(),
                    Ty::TypeVar(member_var.clone()),
                ));

                let typed_expr = TypedExpr::new(expr, Ty::TypeVar(member_var));
                env.typed_exprs.insert(id, typed_expr.clone());
                Ok(typed_expr)
            }
        }
    }

    fn infer_pattern_expr(
        &self,
        id: ExprID,
        env: &mut Environment,
        expr: Expr,
        pattern: &Pattern,
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        let Some(expected) = expected else {
            return Err(TypeError::Unknown(
                "Pattern is missing an expected type (from scrutinee).",
            ));
        };

        self.infer_pattern(pattern, env, expected);
        let typed_expr = TypedExpr::new(expr, expected.clone());
        env.typed_exprs.insert(id, typed_expr.clone());
        Ok(typed_expr)
    }

    fn infer_pattern(&self, pattern: &Pattern, env: &mut Environment, expected: &Ty) {
        log::trace!("Inferring pattern: {:?}", pattern);
        match pattern {
            Pattern::LiteralInt(_) => todo!(),
            Pattern::LiteralFloat(_) => todo!(),
            Pattern::LiteralTrue => todo!(),
            Pattern::LiteralFalse => todo!(),
            Pattern::Bind(name) => {
                log::info!("inferring bind pattern: {:?}", name);
                if let Name::Resolved(symbol_id, _) = name {
                    // Use the expected type for this binding
                    let scheme = env.generalize(expected);
                    env.declare(*symbol_id, scheme);
                }
            }
            Pattern::Wildcard => todo!(),
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                // The expected type should be an Enum type

                // if let Ty::Enum(enum_id, type_args) =
                match expected {
                    Ty::Enum(enum_id, type_args) => {
                        // Look up the enum definition to find this variant
                        if let Some(TypeDef::Enum(enum_def)) = env.types.get(enum_id) {
                            // Find the variant by name
                            if let Some(variant) = enum_def.variants.iter().find(|v| {
                                // Match variant name (comparing the raw string)
                                if let Name::Raw(name_str) = variant_name {
                                    v.name == *name_str
                                } else {
                                    false
                                }
                            }) {
                                // Now we have the variant definition and the concrete type arguments
                                // We need to substitute the enum's type parameters with the actual type args

                                // Create substitution map: enum type param -> concrete type arg
                                let mut substitutions = HashMap::new();
                                for (param_ty, arg_ty) in
                                    enum_def.type_parameters.iter().zip(type_args.iter())
                                {
                                    if let Ty::TypeVar(param_id) = param_ty {
                                        substitutions.insert(param_id.clone(), arg_ty.clone());
                                    }
                                }

                                // Apply substitutions to get concrete field types
                                let concrete_field_types: Vec<Ty> = variant
                                    .values
                                    .iter()
                                    .map(|field_ty| {
                                        env.substitute_ty_with_map(field_ty.clone(), &substitutions)
                                    })
                                    .collect();

                                // Now match field patterns with their concrete types
                                for (field_pattern, field_ty) in
                                    fields.iter().zip(concrete_field_types.iter())
                                {
                                    self.infer_pattern(field_pattern, env, field_ty);
                                }
                            }
                        }
                    }
                    Ty::TypeVar(_) => {
                        // The expected type is still a type variable, so we can't look up variant info yet
                        // Just bind any field patterns to fresh type variables
                        for field_pattern in fields {
                            let field_ty = Ty::TypeVar(env.new_type_variable(
                                TypeVarKind::PatternBind(Name::Raw("field".into())),
                            ));
                            self.infer_pattern(field_pattern, env, &field_ty);
                        }
                    }
                    _ => panic!("Unhandled pattern variant: {:?}", pattern),
                }
            }
        }
    }

    fn hoist_enums(
        &self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), TypeError> {
        for id in root_ids.iter() {
            let expr = source_file.get(*id).unwrap().clone();

            if let Expr::EnumDecl(Name::Resolved(enum_id, _), generics, body) = expr.clone() {
                let Some(Expr::Block(expr_ids)) = source_file.get(body).cloned() else {
                    unreachable!()
                };

                env.start_scope();
                let mut generic_vars = vec![];
                for generic_id in generics.clone() {
                    let ty = self.infer_node(generic_id, env, &None, source_file)?.ty;
                    generic_vars.push(ty);
                }

                let enum_ty = Ty::Enum(enum_id, generic_vars.clone());
                let scheme = env.generalize(&enum_ty);
                log::trace!("enum scheme: {:?}", scheme);
                env.declare_in_parent(enum_id, scheme);

                let mut variants: Vec<Ty> = vec![];
                let mut variant_defs: Vec<EnumVariant> = vec![];

                log::debug!("Generic vars: {:?}", generic_vars);
                for expr_id in expr_ids {
                    let expr = source_file.get(expr_id).cloned().unwrap();
                    if let Expr::EnumVariant(Name::Raw(name_str), values) =
                        source_file.get(expr_id).cloned().unwrap()
                    {
                        let values: Vec<Ty> = values
                            .iter()
                            .map(|id| self.infer_node(*id, env, &None, source_file).unwrap().ty)
                            .collect();
                        let ty = Ty::EnumVariant(enum_id, values.clone());

                        let constructor_symbol = source_file.add_symbol(
                            name_str.clone(),
                            crate::SymbolKind::VariantConstructor,
                            expr_id,
                        );

                        let enum_ty = Ty::Enum(enum_id, generic_vars.clone()); // e.g., Option<TypeVar_for_T>
                        let mut enum_type_unbound_vars = Vec::new();
                        let ftv_in_enum_ty = free_type_vars(&enum_ty); // Should contain TypeVar_for_T

                        for enum_tp_var_instance in &generic_vars {
                            // Iterate over [TypeVar_for_T]
                            if let Ty::TypeVar(tv_id) = enum_tp_var_instance {
                                if ftv_in_enum_ty.contains(tv_id) {
                                    // Check if T is actually in Option<T> (it is)
                                    if !enum_type_unbound_vars.contains(tv_id) {
                                        enum_type_unbound_vars.push(tv_id.clone());
                                    }
                                }
                            }
                        }

                        let scheme_for_enum_type =
                            Scheme::new(enum_ty.clone(), enum_type_unbound_vars.clone()); // Use the collected unbound_vars

                        if env.scopes.len() > 1 && !env.scopes.last().unwrap().is_empty() {
                            env.declare_in_parent(enum_id, scheme_for_enum_type);
                        } else {
                            env.declare(enum_id, scheme_for_enum_type);
                        }

                        env.typed_exprs.insert(
                            expr_id,
                            TypedExpr {
                                expr: expr.clone(),
                                ty: ty.clone(),
                            },
                        );

                        variants.push(ty);
                        variant_defs.push(EnumVariant {
                            name: name_str.to_string(),
                            values,
                            constructor_symbol,
                        });
                    } else {
                        log::debug!("Non-raw expr: {:?}", source_file.get(expr_id).unwrap());
                    }
                }
                env.end_scope();

                log::debug!(
                    "Registering enum {:?}, variants: {:?}",
                    enum_id,
                    variant_defs
                );
                env.register_enum(EnumDef {
                    name: Some(enum_id),
                    variants: variant_defs,
                    type_parameters: generic_vars,
                    methods: vec![],
                });

                let typed_expr = TypedExpr::new(expr, enum_ty.clone());
                env.typed_exprs.insert(*id, typed_expr);
            }
        }

        Ok(())
    }

    fn hoist_functions(
        &self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &SourceFile<NameResolved>,
    ) {
        for id in root_ids.iter() {
            let expr = source_file.get(*id).unwrap().clone();

            if let Expr::Func(
                Some(FuncName::Resolved(symbol_id)),
                ref _generics,
                ref _params,
                _body,
                _ret,
            ) = expr
            {
                let fn_var =
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncNameVar(symbol_id)));

                let typed_expr = TypedExpr::new(expr, fn_var.clone());
                env.typed_exprs.insert(*id, typed_expr);

                let scheme = env.generalize(&fn_var);
                env.declare(symbol_id, scheme);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        SourceFile, SymbolID, Typed,
        constraint_solver::ConstraintSolver,
        expr::Expr,
        name::Name,
        name_resolver::NameResolver,
        parser::parse,
        type_checker::{Ty, TypeVarID, TypeVarKind},
    };

    use super::TypeChecker;

    fn check(code: &'static str) -> SourceFile<Typed> {
        let parsed = parse(code).unwrap();
        let resolver = NameResolver::default();
        let resolved = resolver.resolve(parsed);
        let checker = TypeChecker;
        let mut inferred = checker.infer(resolved).unwrap();
        let mut constraint_solver = ConstraintSolver::new(&mut inferred);
        constraint_solver.solve().unwrap();
        inferred
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

        // g's return type (B) must match f's argument type
        assert_eq!(*g_ret, f_args[0].clone());

        // the inner function's return (and thus compose's return) is f's return type C
        let Ty::Func(inner_params, inner_ret) = *return_type else {
            panic!(
                "expected `compose` to return a function, got {:?}",
                return_type
            );
        };
        assert_eq!(inner_params.len(), 1);
        assert_eq!(inner_params[0], g_args[0].clone()); // inner's x : A
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

    #[test]
    fn checks_simple_enum_declaration() {
        let checker = check(
            "
            enum Fizz {
                case foo, bar
            }
        ",
        );

        assert_eq!(
            checker.type_for(checker.root_ids()[0]),
            Ty::Enum(SymbolID::at(1), vec![])
        );

        // Check the variants
        assert_eq!(
            checker.type_for(0),
            Ty::EnumVariant(SymbolID::at(1), vec![])
        );
        assert_eq!(
            checker.type_for(1),
            Ty::EnumVariant(SymbolID::at(1), vec![])
        );
    }

    #[test]
    fn checks_enum_with_associated_values() {
        let checker = check(
            "
            enum Option {
                case some(Int), none
            }
            ",
        );

        assert_eq!(
            checker.type_for(checker.root_ids()[0]),
            Ty::Enum(SymbolID::at(1), vec![])
        );

        // Check variant types
        assert_eq!(
            checker.type_for(1),
            Ty::EnumVariant(SymbolID::at(1), vec![Ty::Int]),
        );
        assert_eq!(
            checker.type_for(2),
            Ty::EnumVariant(SymbolID::at(1), vec![])
        );
    }

    #[test]
    fn checks_generic_enum_declaration() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none
            }
            ",
        );

        let enum_ty = checker.type_for(checker.root_ids()[0]);
        match enum_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::at(1));
                assert_eq!(generics.len(), 1);
                // Should be a type variable for T
                assert!(matches!(generics[0], Ty::TypeVar(_)));
            }
            _ => panic!("Expected generic enum type, got {:?}", enum_ty),
        }
    }

    #[test]
    fn checks_enum_variant_constructor_call() {
        let checker = check(
            "
            enum Option {
                case some(Int), none
            }

            Option.some(42)
            ",
        );

        // The call to some(42) should return Option type
        let call_result = checker.type_for(checker.root_ids()[1]);
        assert_eq!(call_result, Ty::Enum(SymbolID::at(1), vec![]));
    }

    #[test]
    fn checks_generic_enum_variant_constructor() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none  
            }
            Option.some(42)
            Option.some(3.14)
            ",
        );

        // First call should be Option<Int>
        let call1 = checker.type_for(checker.root_ids()[1]);
        match call1 {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::at(1));
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Option<Int>, got {:?}", call1),
        }

        // Second call should be Option<Float>
        let call2 = checker.type_for(checker.root_ids()[2]);
        match call2 {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::at(1));
                assert_eq!(generics, vec![Ty::Float]);
            }
            _ => panic!("Expected Option<Float>, got {:?}", call2),
        }
    }

    #[test]
    fn checks_nested_enum_types() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none
            }

            enum Result<T, E> {
                case ok(T), err(E)
            }
            Result.ok(Option.some(42))
            ",
        );

        // Should be Result<Option<Int>, _>
        let result_ty = checker.type_for(checker.root_ids()[2]);
        match result_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::at(3)); // Result enum
                assert_eq!(generics.len(), 2);

                // First generic should be Option<Int>
                match &generics[0] {
                    Ty::Enum(opt_id, opt_generics) => {
                        assert_eq!(*opt_id, SymbolID::at(1)); // Option enum
                        assert_eq!(opt_generics, &vec![Ty::Int]);
                    }
                    _ => panic!("Expected Option<Int> as first generic"),
                }
            }
            _ => panic!("Expected Result type, got {:?}", result_ty),
        }
    }

    #[test]
    fn checks_basic_match_expression() {
        let checker = check(
            "
            enum Bool {
                case yes, no
            }

            func test(b: Bool) {
                match b {
                    .yes -> 1
                    .no -> 0
                }
            }
            ",
        );

        // Function should have type Bool -> Int
        let func_ty = checker.type_for(checker.root_ids()[1]);
        match func_ty {
            Ty::Func(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], Ty::Enum(SymbolID::at(1), vec![])); // Bool
                assert_eq!(*ret, Ty::Int);
            }
            _ => panic!("Expected function type, got {:?}", func_ty),
        }
    }

    #[test]
    fn checks_match_with_variable_binding() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none
            }
            func unwrap(opt: Option<Int>) {
                match opt {
                    .some(value) -> value
                    .none -> 0
                }
            }
            ",
        );

        // Function should have type Option<Int> -> Int
        let func_ty = checker.type_for(checker.root_ids()[1]);
        match func_ty {
            Ty::Func(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], Ty::Enum(SymbolID::at(1), vec![Ty::Int])); // Option<Int>
                assert_eq!(*ret, Ty::Int);
            }
            _ => panic!("Expected function type, got {:?}", func_ty),
        }
    }

    #[test]
    fn checks_recursive_enum() {
        let checker = check(
            "
            enum List<T> {
                case cons(T, List<T>), nil
            }
            ",
        );

        let enum_ty = checker.type_for(checker.root_ids()[0]);
        match enum_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::at(1));
                assert_eq!(generics.len(), 1);
            }
            _ => panic!("Expected List<T> type, got {:?}", enum_ty),
        }

        let Some(Expr::EnumDecl(_, _, body)) = checker.roots()[0] else {
            panic!("did not get enum decl");
        };

        assert_eq!(*body, 6);

        let Some(Expr::Block(exprs)) = checker.get(6) else {
            panic!("did not get body");
        };

        assert_eq!(exprs[0], 4);

        // Check cons variant has recursive structure: T, List<T>
        let cons_variant = checker.type_for(4);
        match cons_variant {
            Ty::EnumVariant(enum_id, field_types) => {
                assert_eq!(enum_id, SymbolID::at(1));
                assert_eq!(field_types.len(), 2);
                // Second field should be List<T> (recursive reference)
                match &field_types[1] {
                    Ty::Enum(list_id, _) => assert_eq!(*list_id, SymbolID::at(1)),
                    _ => panic!("Expected recursive List type"),
                }
            }
            _ => panic!("Expected cons variant type, got: {:?}", cons_variant),
        }
    }

    #[test]
    fn checks_match_type_mismatch_error() {
        // This should fail due to inconsistent return types in match arms
        let result = std::panic::catch_unwind(|| {
            check(
                "
                enum Bool {
                    case true, false  
                }
                func test(b: Bool) {
                    match b {
                        .true -> 1      // Int
                        .false -> 3.14  // Float - type mismatch!
                    }
                }
                ",
            )
        });

        // Should fail type checking
        assert!(result.is_err());
    }

    #[test]
    fn checks_enum_in_function_parameters() {
        let checker = check(
            "
            enum Color {
                case red, green, blue
            }
            func describe(c: Color) -> Int {
                match c {
                    .red -> 1
                    .green -> 2  
                    .blue -> 3
                }
            }
            describe(.red)
            ",
        );

        // Call should type check correctly
        let call_result = checker.type_for(checker.root_ids()[2]);
        assert_eq!(call_result, Ty::Int);
    }

    #[test]
    fn checks_multiple_enum_parameters() {
        let checker = check(
            "
            enum Bool {
                case yes, no
            }
            func and(a: Bool, b: Bool) -> Bool {
                match a {
                    .yes -> b
                    .no -> .no
                }
            }
            and(.yes, .no)
            ",
        );

        let call_result = checker.type_for(checker.root_ids()[2]);
        assert_eq!(call_result, Ty::Enum(SymbolID::at(1), vec![])); // Bool
    }

    #[test]
    fn checks_enum_as_return_type() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none
            }
            func create_some(x: Int) -> Option<Int> {
                .some(x)
            }
            create_some(42)
            ",
        );

        let call_result = checker.type_for(checker.root_ids()[2]);
        assert_eq!(call_result, Ty::Enum(SymbolID::at(1), vec![Ty::Int])); // Option<Int>
    }

    #[test]
    fn checks_complex_generic_constraints() {
        let checker = check(
            "
            enum Either<L, R> {
                case left(L), right(R)
            }
            func swap(e: Either<Int, Float>) -> Either<Float, Int> {
                match e {
                    .left(i) -> .right(i)
                    .right(f) -> .left(f)
                }
            }
            ",
        );

        let func_ty = checker.type_for(checker.root_ids()[1]);
        match func_ty {
            Ty::Func(params, ret) => {
                // Input: Either<Int, Float>
                assert_eq!(
                    params[0],
                    Ty::Enum(SymbolID::at(1), vec![Ty::Int, Ty::Float])
                );
                // Output: Either<Float, Int>
                assert_eq!(*ret, Ty::Enum(SymbolID::at(1), vec![Ty::Float, Ty::Int]));
            }
            _ => panic!("Expected function type"),
        }
    }

    #[test]
    fn checks_builtin_optional() {
        let checker = check(
            "
        let x = Optional.some(42)
        let y = Optional.none
        
        match x {
            .some(val) -> val
            .none -> 0
        }
        ",
        );

        // x should be Optional<Int>
        let x_ty = checker.type_for(checker.root_ids()[0]);
        match x_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::at(-3)); // Optional's ID
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Optional<Int>, got {:?}", x_ty),
        }

        // The match should return Int
        let match_ty = checker.type_for(checker.root_ids()[2]);
        assert_eq!(match_ty, Ty::Int);
    }

    #[test]
    fn checks_polymorphic_match() {
        let checker = check(
            "
            func map<U, T>(opt: T?, f: (T) -> U) -> U? {
                match opt {
                    .some(value) -> .some(f(value))
                    .none -> .none
                }
            }

            map(.some(123), func(foo) { foo })
            ",
        );

        // Should type check without errors - polymorphic function
        // map : ∀T,U. Option<T> -> (T -> U) -> Option<U>
        let Ty::Func(args, ret) = checker.type_for(checker.root_ids()[0]) else {
            panic!("did not get func")
        };

        assert_eq!(
            args[0],
            Ty::Enum(
                SymbolID(1),
                vec![Ty::TypeVar(TypeVarID(
                    4,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::at(3), "T".into()))
                ))]
            )
        );
        assert_eq!(
            args[1],
            Ty::Func(
                vec![Ty::TypeVar(TypeVarID(
                    4,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::at(3), "T".into()))
                ))],
                Ty::TypeVar(TypeVarID(
                    3,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::at(2), "U".into()))
                ))
                .into()
            )
        );
        assert_eq!(
            ret,
            Ty::Enum(
                SymbolID(1),
                vec![Ty::TypeVar(TypeVarID(
                    3,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID(6), "U".into()))
                ))]
            )
            .into()
        );

        let call_result = checker.type_for(checker.root_ids()[1]);
        match call_result {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::at(-3)); // Optional's ID
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Optional<Int>, got {:?}", call_result),
        }
    }
}

// #[cfg(test)]
// mod pending {
//     use crate::{constraint_solver::ConstraintSolver, name_resolver::NameResolver, parser::parse};

//     use super::{Ty, TypeChecker};

//     fn check(code: &'static str) -> Ty {
//         let parsed = parse(code).unwrap();
//         let resolver = NameResolver::default();
//         let resolved = resolver.resolve(parsed);
//         let checker = TypeChecker;
//         let mut inferred = checker.infer(resolved).unwrap();
//         let mut constraint_solver = ConstraintSolver::new(&mut inferred);
//         constraint_solver.solve().unwrap();
//         inferred.type_for(inferred.root_ids()[0])
//     }

//     #[test]
//     fn checks_match_exhaustiveness_error() {
//         // This should fail type checking due to non-exhaustive match
//         let result = std::panic::catch_unwind(|| {
//             check(
//                 "
//                 enum Bool {
//                     case yes, no
//                 }
//                 func test(b: Bool) -> Int {
//                     match b {
//                         .yes -> 1
//                     }
//                 }
//                 ",
//             )
//         });

//         // Should panic or return error - depends on your error handling
//         assert!(result.is_err());
//     }

//     #[test]
//     fn checks_literal_true() {
//         assert_eq!(check("true"), Ty::Bool);
//     }

//     #[test]
//     fn checks_literal_false() {
//         check("false");
//     }

//     #[test]
//     #[should_panic]
//     fn checks_if_expression() {
//         check("if true { 1 } else { 0 }");
//     }

//     #[test]
//     #[should_panic]
//     fn checks_loop_expression() {
//         check("loop { 1 }");
//     }

//     #[test]
//     #[should_panic]
//     fn checks_tuple_expression() {
//         check("(1, true)");
//     }

//     #[test]
//     #[should_panic]
//     fn checks_unary_expression() {
//         check("-1"); // Assuming '-' is a unary op
//     }

//     #[test]
//     #[should_panic]
//     fn checks_binary_expression() {
//         check("1 + 2");
//     }

//     #[test]
//     fn checks_pattern_literal_int_in_match() {
//         check(
//             "
//             enum MyEnum {
//                 case val(Int)
//             }
//             func test(e: MyEnum) {
//                 match e {
//                     .val(1) -> 0
//                 }
//             }
//         ",
//         );
//     }

//     #[test]
//     #[should_panic]
//     fn checks_pattern_wildcard_in_match() {
//         check(
//             "
//             enum MyEnum { case Val(Int) }
//             func test(e: MyEnum) {
//                 match e {
//                     _ -> 0 // Pattern::Wildcard
//                 }
//             }
//         ",
//         );
//     }
// }
