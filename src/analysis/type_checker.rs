use std::collections::HashMap;

use crate::{
    NameResolved, SymbolID, SymbolTable, Typed,
    diagnostic::Diagnostic,
    environment::{EnumVariant, Method, Property, StructDef, free_type_vars},
    expr::{Expr, Pattern},
    match_builtin,
    name::Name,
    name_resolver::NameResolverError,
    parser::ExprID,
    prelude::compile_prelude,
    source_file::SourceFile,
    token_kind::TokenKind,
};

use super::{
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
    Element,
    VariantValue,
    PatternBind(Name),
}

#[derive(Debug, PartialEq, Clone)]
pub enum TypeError {
    Unresolved,
    InvalidEnumAccess,
    NameResolution(NameResolverError),
    UnknownEnum(SymbolID),
    UnknownVariant(Name),
    Unknown(&'static str),
    UnexpectedType(Ty, Ty),
    Mismatch(Ty, Ty),
    OccursConflict,
}

#[derive(Clone, PartialEq, Debug, Eq)]
pub enum Ty {
    Void,
    Int,
    Bool,
    Float,
    Func(
        FuncParams,    /* params */
        FuncReturning, /* returning */
        Vec<Ty>,       /* generics */
    ),
    Closure {
        func: Box<Ty>, // the func
        captures: Vec<Ty>,
    },
    TypeVar(TypeVarID),
    Enum(SymbolID, Vec<Ty>), // enum name + type arguments
    EnumVariant(SymbolID /* Enum */, Vec<Ty> /* Values */),
    Tuple(Vec<Ty>),
    Array(Box<Ty>),
    Struct(SymbolID, Vec<Ty> /* generics */),
}

impl Ty {
    fn optional(&self) -> Ty {
        Ty::Enum(SymbolID::OPTIONAL, vec![self.clone()])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
pub struct TypeChecker;

fn checked_expected(expected: &Option<Ty>, actual: Ty) -> Result<Ty, TypeError> {
    if let Some(expected) = expected {
        match (&actual, expected) {
            (Ty::TypeVar(_), _) | (_, Ty::TypeVar(_)) => (),
            (typ, expected) => {
                if typ != expected {
                    return Err(TypeError::UnexpectedType(expected.clone(), actual.clone()));
                }
            }
        }
    }

    Ok(actual)
}

impl TypeChecker {
    pub fn infer(
        &self,
        source_file: SourceFile<NameResolved>,
        symbol_table: &mut SymbolTable,
        env: &mut Environment,
    ) -> SourceFile<Typed> {
        env.import_prelude(compile_prelude());
        self.infer_without_prelude(env, source_file, symbol_table)
    }

    pub fn infer_without_prelude(
        &self,
        env: &mut Environment,
        mut source_file: SourceFile<NameResolved>,
        symbol_table: &mut SymbolTable,
    ) -> SourceFile<Typed> {
        let root_ids = source_file.root_ids();

        match self.hoist_structs(&root_ids, env, &mut source_file, symbol_table) {
            Err(e) => source_file.diagnostics.push(Diagnostic::typing(e)),
            _ => (),
        }

        match self.hoist_enums(&root_ids, env, &mut source_file, symbol_table) {
            Err(e) => source_file.diagnostics.push(Diagnostic::typing(e)),
            _ => (),
        }

        self.hoist_functions(&root_ids, env, &source_file);

        let mut typed_roots = vec![];
        for id in &root_ids {
            self.infer_node(id, env, &None, &mut source_file);
            typed_roots.push(env.typed_exprs.get(id).unwrap().clone())
        }

        // Now it's safe to move source_file since env is dropped before this line
        source_file.to_typed(typed_roots, env.clone())
    }

    pub fn infer_node(
        &self,
        id: &ExprID,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let expr = source_file.get(id).unwrap().clone();
        log::trace!("Inferring {expr:?}");

        let ty = match &expr {
            Expr::LiteralTrue | Expr::LiteralFalse => checked_expected(expected, Ty::Bool),
            Expr::Loop(cond, body) => self.infer_loop(cond, body, env, source_file),
            Expr::If(condition, consequence, alternative) => {
                let ty = self.infer_if(condition, consequence, alternative, env, source_file);
                if let Ok(ty) = &ty {
                    checked_expected(expected, ty.clone());
                }

                ty
            }
            Expr::Call {
                callee,
                type_args,
                args,
            } => self.infer_call(env, callee, type_args, args, expected, source_file),
            Expr::LiteralInt(_) => checked_expected(expected, Ty::Int),
            Expr::LiteralFloat(_) => checked_expected(expected, Ty::Float),
            Expr::Assignment(lhs, rhs) => self.infer_assignment(env, lhs, rhs, source_file),
            Expr::TypeRepr(name, generics, is_type_parameter) => {
                self.infer_type_repr(env, name, generics, is_type_parameter, source_file)
            }
            Expr::FuncTypeRepr(args, ret, _is_type_parameter) => {
                self.infer_func_type_repr(env, args, ret, expected, source_file)
            }
            Expr::TupleTypeRepr(types, _is_type_parameter) => {
                self.infer_tuple_type_repr(env, types, expected, source_file)
            }
            Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                captures,
                ..
            } => self.infer_func(
                id,
                env,
                name,
                generics,
                params,
                captures,
                body,
                ret,
                expected,
                source_file,
            ),
            Expr::Let(Name::Resolved(symbol_id, _), rhs) => {
                self.infer_let(env, *symbol_id, rhs, source_file)
            }
            Expr::Variable(Name::Resolved(symbol_id, name), _) => {
                self.infer_variable(env, *symbol_id, name)
            }
            Expr::Parameter(_, _) => {
                panic!("unresolved parameter: {:?}", source_file.get(id).unwrap())
            }
            Expr::Tuple(types) => self.infer_tuple(types, env, source_file),
            Expr::Unary(_token_kind, rhs) => self.infer_unary(rhs, expected, env, source_file),
            Expr::Binary(lhs, op, rhs) => {
                self.infer_binary(id, lhs, rhs, op, expected, env, source_file)
            }
            Expr::Block(items) => self.infer_block(id, env, items, expected, source_file),
            Expr::EnumDecl(_, _generics, _body) => Ok(env.typed_exprs.get(id).unwrap().clone().ty),
            Expr::EnumVariant(_, _) => Ok(env.typed_exprs.get(id).unwrap().clone().ty),
            Expr::Match(pattern, items) => self.infer_match(env, pattern, items, source_file),
            Expr::MatchArm(pattern, body) => {
                self.infer_match_arm(env, pattern, body, expected, source_file)
            }
            Expr::PatternVariant(_, _, _items) => self.infer_pattern_variant(id, env),
            Expr::Member(receiver, member_name) => {
                self.infer_member(id, env, receiver, member_name, source_file)
            }
            Expr::Pattern(pattern) => self.infer_pattern_expr(env, pattern, expected, source_file),
            Expr::Variable(Name::Raw(_), _) => Err(TypeError::Unresolved),
            Expr::Variable(Name::_Self(sym), _) => Ok(env.instantiate_symbol(*sym)),
            Expr::Return(rhs) => self.infer_return(rhs, env, expected, source_file),
            Expr::LiteralArray(items) => self.infer_array(items, env, expected, source_file),
            _ => panic!("Unhandled expr in type checker: {:?}", expr.clone()),
        };

        match &ty {
            Ok(ty) => {
                let typed_expr = TypedExpr {
                    id: *id,
                    expr,
                    ty: ty.clone(),
                };

                env.typed_exprs.insert(*id, typed_expr);
            }
            Err(e) => source_file.diagnostics.push(Diagnostic::typing(e.clone())),
        }

        ty
    }

    fn infer_array(
        &self,
        items: &[ExprID],
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let mut tys: Vec<Ty> = vec![];
        for i in items {
            tys.push(self.infer_node(i, env, expected, source_file)?.clone());
        }

        // TODO: error when the tys don't match
        let ty = tys
            .into_iter()
            .last()
            .unwrap_or_else(|| Ty::TypeVar(env.new_type_variable(TypeVarKind::Element)));

        Ok(Ty::Array(Box::new(ty)))
    }

    fn infer_return(
        &self,
        rhs: &Option<ExprID>,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        if let Some(rhs) = rhs {
            self.infer_node(rhs, env, expected, source_file)
        } else {
            Ok(Ty::Void)
        }
    }

    fn infer_loop(
        &self,
        cond: &Option<ExprID>,
        body: &ExprID,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        if let Some(cond) = cond {
            self.infer_node(cond, env, &Some(Ty::Bool), source_file)?;
        }

        self.infer_node(body, env, &None, source_file)?;

        Ok(Ty::Void)
    }

    fn infer_if(
        &self,
        condition: &ExprID,
        consequence: &ExprID,
        alternative: &Option<ExprID>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let _condition = self.infer_node(condition, env, &Some(Ty::Bool), source_file)?;
        let consequence = self.infer_node(consequence, env, &None, source_file)?;
        if let Some(alternative_id) = alternative {
            let alternative = self.infer_node(alternative_id, env, &None, source_file)?;
            env.constrain_equality(*alternative_id, consequence.clone(), alternative);
            Ok(consequence)
        } else {
            Ok(consequence.optional())
        }
    }

    fn infer_call(
        &self,
        env: &mut Environment,
        callee: &ExprID,
        type_args: &[ExprID],
        args: &[ExprID],
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let ret_var = if let Some(expected) = expected {
            expected.clone()
        } else {
            // Avoid borrow checker issue by creating the type variable before any borrows
            let call_return_var = env.new_type_variable(TypeVarKind::CallReturn);
            Ty::TypeVar(call_return_var)
        };

        let mut inferred_type_args = vec![];
        for type_arg in type_args {
            inferred_type_args.push(self.infer_node(type_arg, env, expected, source_file)?);
        }

        let mut arg_tys: Vec<Ty> = vec![];
        for arg in args {
            let ty = self.infer_node(arg, env, &None, source_file).unwrap();
            arg_tys.push(ty);
        }

        let expected_callee_ty = Ty::Func(arg_tys, Box::new(ret_var.clone()), inferred_type_args);
        let callee_ty = self.infer_node(callee, env, &None, source_file)?;

        env.constrain_equality(*callee, expected_callee_ty, callee_ty.clone());

        Ok(ret_var)
    }

    fn infer_assignment(
        &self,
        env: &mut Environment,
        lhs: &ExprID,
        rhs: &ExprID,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let lhs_ty = self.infer_node(lhs, env, &None, source_file)?;
        let rhs_ty = self.infer_node(rhs, env, &None, source_file)?;

        env.constrain_equality(*lhs, lhs_ty.clone(), rhs_ty);

        Ok(lhs_ty)
    }

    fn infer_type_repr(
        &self,
        env: &mut Environment,
        name: &Name,
        generics: &[ExprID],
        is_type_parameter: &bool,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let name = name.clone();

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
                    if *is_type_parameter {
                        Ty::TypeVar(env.new_type_variable(TypeVarKind::TypeRepr(name.clone())))
                    } else {
                        // Attempting to use an unresolved raw name as a type.
                        // This should ideally be an error or a placeholder needing resolution.
                        // For now, create a type variable, similar to previous behavior.
                        log::warn!("Encountered unresolved raw type name in usage: {raw_name:?}");
                        Ty::TypeVar(env.new_type_variable(TypeVarKind::TypeRepr(name.clone())))
                    }
                }
            }
            Name::Resolved(symbol_id, name_str) => {
                if let Some(builtin_ty) =
                    match_builtin(&Name::Resolved(*symbol_id, name_str.clone()))
                {
                    builtin_ty
                } else if *is_type_parameter {
                    // Declaration site of a type parameter (e.g., T in `enum Option<T>`).
                    // Create a new type variable for it.
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::TypeRepr(name.clone())))
                } else {
                    // Usage of a resolved type name (e.g., T in `case some(T)` or `Int`).
                    // Instantiate its scheme from the environment.
                    env.instantiate_symbol(*symbol_id)
                }
            }
            Name::_Self(symbol_id) => env.instantiate_symbol(*symbol_id),
        };

        // For explicit lists of generic types like <Int> in Option<Int>, we need to handle the generics
        if !generics.is_empty() && !is_type_parameter {
            // First, infer all the generic arguments
            let mut generic_types = Vec::new();
            for generic_id in generics {
                let generic_ty = self.infer_node(generic_id, env, &None, source_file)?;
                generic_types.push(generic_ty);
            }

            // Now when we have a resolved symbol for a generic type
            if let Name::Resolved(symbol_id, _) = name {
                let ty = match env.lookup_type(&symbol_id) {
                    Some(TypeDef::Enum(_)) => Ty::Enum(symbol_id, generic_types),
                    Some(TypeDef::Struct(def)) => def.type_repr(&generic_types),
                    _ => panic!(
                        "Didn't get type for symbol {:?} {:?}",
                        symbol_id,
                        env.lookup_enum(&symbol_id)
                    ),
                };

                // Instead of just instantiating, we need to build the concrete type
                // For enums, this means Ty::Enum(symbol_id, generic_types)
                return Ok(ty);
            }
        }

        if *is_type_parameter {
            // This is for the T in `enum Option<T>`. Name should be resolved by name_resolver.
            let Name::Resolved(symbol_id, _) = name else {
                panic!("Type parameter name {name:?} was not resolved during its declaration")
            };
            log::debug!("Declaring type parameter {symbol_id:?} ({name:?}) with ty {ty:?}");
            // Type parameters are monomorphic within their defining generic scope.
            // So, references to this type parameter within this scope refer to this 'ty'.
            env.declare(symbol_id, Scheme::new(ty.clone(), vec![]));
        }

        Ok(ty)
    }

    fn infer_func_type_repr(
        &self,
        env: &mut Environment,
        args: &[ExprID],
        ret: &ExprID,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let mut inferred_args = vec![];
        for arg in args {
            inferred_args.push(self.infer_node(arg, env, expected, source_file)?);
        }

        let inferred_ret = self.infer_node(ret, env, expected, source_file)?;

        let ty = Ty::Func(inferred_args, Box::new(inferred_ret), vec![]);
        Ok(ty)
    }

    fn infer_tuple_type_repr(
        &self,
        env: &mut Environment,
        types: &Vec<ExprID>,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let mut inferred_types: Vec<Ty> = vec![];
        for t in types {
            inferred_types.push(self.infer_node(t, env, expected, source_file)?);
        }
        Ok(Ty::Tuple(inferred_types))
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_func(
        &self,
        id: &ExprID,
        env: &mut Environment,
        name: &Option<Name>,
        generics: &[ExprID],
        params: &[ExprID],
        captures: &[SymbolID],
        body: &ExprID,
        ret: &Option<ExprID>,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let mut func_var = None;

        if let Some(Name::Resolved(symbol_id, _)) = name {
            let type_var = env.new_type_variable(TypeVarKind::FuncNameVar(*symbol_id));
            func_var = Some(type_var.clone());
            let scheme = env.generalize(&Ty::TypeVar(type_var));
            env.declare(*symbol_id, scheme);
            log::debug!("Declared scheme for named func {symbol_id:?}, {env:?}");
        }

        env.start_scope();

        let mut inferred_generics = vec![];
        for generic in generics {
            inferred_generics.push(self.infer_node(generic, env, expected, source_file)?);
        }

        // Infer generic type parameters
        let mut generic_vars = vec![];
        for generic_id in generics {
            let ty = self.infer_node(generic_id, env, &None, source_file)?;
            generic_vars.push(ty);

            // If this is a type parameter declaration, we need to declare it in the environment
            if let Expr::TypeRepr(Name::Resolved(symbol_id, _), _, true) =
                source_file.get(generic_id).unwrap()
            {
                // The type was already created by infer_node, so we just need to get it
                if let Some(typed_expr) = env.typed_exprs.get(generic_id) {
                    env.declare(*symbol_id, Scheme::new(typed_expr.ty.clone(), vec![]));
                }
            }
        }

        let expected_body_ty = if let Some(ret) = ret {
            Some(self.infer_node(ret, env, &None, source_file)?)
        } else {
            None
        };

        let ret_ty: Option<Ty> = ret
            .as_ref()
            .map(|repr| self.infer_node(repr, env, &None, source_file))
            .transpose()
            .unwrap_or(None);

        let mut param_vars: Vec<Ty> = vec![];
        for expr_opt in params.iter() {
            let expr = source_file.get(expr_opt).cloned();
            if let Some(Expr::Parameter(Name::Resolved(symbol_id, _), ty)) = expr {
                let var_ty = if let Some(ty_id) = &ty {
                    self.infer_node(ty_id, env, expected, source_file)?
                } else {
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncParam))
                };

                // Parameters are monomorphic inside the function body
                let scheme = Scheme::new(var_ty.clone(), vec![]);
                env.declare(symbol_id, scheme);
                param_vars.push(var_ty.clone());
                env.typed_exprs.insert(
                    *expr_opt,
                    TypedExpr {
                        id: *expr_opt,
                        expr: expr.unwrap(),
                        ty: var_ty,
                    },
                );
            }
        }

        let body_ty = self.infer_node(body, env, &expected_body_ty, source_file)?;

        if let Some(ret_type) = ret_ty {
            env.constrain_equality(ret.unwrap(), body_ty.clone(), ret_type);
        }

        env.end_scope();

        let func_ty = Ty::Func(param_vars.clone(), Box::new(body_ty), inferred_generics);
        let inferred_ty = if captures.is_empty() {
            func_ty
        } else {
            let capture_tys = captures
                .iter()
                .map(|c| env.instantiate_symbol(*c))
                .collect();

            Ty::Closure {
                func: func_ty.into(),
                captures: capture_tys,
            }
        };

        if let Some(func_var) = func_var {
            env.constrain_equality(*id, Ty::TypeVar(func_var), inferred_ty.clone());

            if let Some(Name::Resolved(symbol_id, _)) = name {
                let scheme = if env.scopes.len() > 1 {
                    Scheme::new(inferred_ty.clone(), vec![])
                } else {
                    env.generalize(&inferred_ty)
                };
                env.scopes.last_mut().unwrap().insert(*symbol_id, scheme);
            }
        }

        Ok(inferred_ty)
    }

    fn infer_let(
        &self,
        env: &mut Environment,
        symbol_id: SymbolID,
        rhs: &Option<ExprID>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let rhs_ty = if let Some(rhs) = rhs {
            self.infer_node(rhs, env, &None, source_file)?
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

        Ok(rhs_ty)
    }

    fn infer_variable(
        &self,
        env: &mut Environment,
        symbol_id: SymbolID,
        name: &str,
    ) -> Result<Ty, TypeError> {
        let ty = env.instantiate_symbol(symbol_id);
        log::trace!("instantiated {symbol_id:?} ({name:?}) with {ty:?}");
        Ok(ty)
    }

    fn infer_tuple(
        &self,
        types: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        if types.len() == 1 {
            // If it's a single element, don't treat it as a tuple
            return self.infer_node(&types[0], env, &None, source_file);
        }

        let mut inferred_types: Vec<Ty> = vec![];
        for t in types {
            inferred_types.push(self.infer_node(t, env, &None, source_file)?);
        }
        Ok(Ty::Tuple(inferred_types))
    }

    fn infer_unary(
        &self,
        rhs: &ExprID,
        expected: &Option<Ty>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        self.infer_node(rhs, env, expected, source_file)
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_binary(
        &self,
        _id: &ExprID,
        lhs_id: &ExprID,
        rhs_id: &ExprID,
        op: &TokenKind,
        _expected: &Option<Ty>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let lhs = self.infer_node(lhs_id, env, &None, source_file)?;
        let rhs = self.infer_node(rhs_id, env, &None, source_file)?;

        env.constrain_equality(*lhs_id, lhs.clone(), rhs);

        // TODO: For now we're just gonna hardcode these
        use TokenKind::*;
        match op {
            // Bool ops
            EqualsEquals => Ok(Ty::Bool),
            BangEquals => Ok(Ty::Bool),
            Greater => Ok(Ty::Bool),
            GreaterEquals => Ok(Ty::Bool),
            Less => Ok(Ty::Bool),
            LessEquals => Ok(Ty::Bool),

            // Same type ops
            _ => Ok(lhs),
        }
    }

    fn infer_block(
        &self,
        id: &ExprID,
        env: &mut Environment,
        items: &[ExprID],
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        env.start_scope();

        self.hoist_functions(items, env, source_file);

        let mut return_exprs: Vec<(ExprID, Ty)> = vec![];

        let return_ty: Ty = {
            let mut return_ty: Ty = Ty::Void;

            for (i, item) in items.iter().enumerate() {
                let ty = if i == items.len() - 1 {
                    return_ty = self.infer_node(item, env, expected, source_file)?;
                    return_ty.clone()
                } else {
                    self.infer_node(item, env, &None, source_file)?
                };

                if let Some(Expr::Return(_)) = source_file.get(item) {
                    return_exprs.push((*item, ty));
                }
            }

            return_ty
        };

        let return_ty = if let Some(expected) = expected {
            if return_ty != *expected {
                env.constrain_equality(*id, return_ty, expected.clone());
            }

            expected.clone()
        } else {
            return_ty.clone()
        };

        // Make sure all return exprs agree
        for (id, ty) in return_exprs {
            env.constrain_equality(id, ty, return_ty.clone());
        }

        env.end_scope();

        Ok(return_ty)
    }

    fn infer_match(
        &self,
        env: &mut Environment,
        pattern: &ExprID,
        arms: &[ExprID],
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let pattern_ty = self.infer_node(pattern, env, &None, source_file)?;
        let arms_ty = arms
            .iter()
            .map(|id| self.infer_node(id, env, &Some(pattern_ty.clone()), source_file))
            .collect::<Result<Vec<_>, _>>()?;

        // TODO: Make sure the return type is the same for all arms
        let ret_ty = arms_ty.last().unwrap().clone();

        Ok(ret_ty)
    }

    fn infer_match_arm(
        &self,
        env: &mut Environment,
        pattern: &ExprID,
        body: &ExprID,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        env.start_scope();
        let _pattern_ty = self.infer_node(pattern, env, expected, source_file)?;
        let body_ty = self.infer_node(body, env, &None, source_file)?;
        env.end_scope();
        Ok(body_ty)
    }

    fn infer_pattern_variant(&self, _id: &ExprID, _env: &mut Environment) -> Result<Ty, TypeError> {
        todo!()
    }

    fn infer_member(
        &self,
        id: &ExprID,
        env: &mut Environment,
        receiver: &Option<ExprID>,
        member_name: &str,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        match receiver {
            None => {
                // Unqualified: .some
                // Create a type variable that will be constrained later
                let member_var = env.new_type_variable(TypeVarKind::Member);

                env.constrain_unqualified_member(
                    *id,
                    member_name.to_string(),
                    Ty::TypeVar(member_var.clone()),
                );

                Ok(Ty::TypeVar(member_var))
            }
            Some(receiver_id) => {
                // Qualified: Option.some
                let receiver_ty = self.infer_node(receiver_id, env, &None, source_file)?;

                // Create a type variable for the member
                let member_var = env.new_type_variable(TypeVarKind::Member);

                // Add a constraint that links the receiver type to the member
                env.constrain_member(
                    *id,
                    receiver_ty,
                    member_name.to_string(),
                    Ty::TypeVar(member_var.clone()),
                );

                Ok(Ty::TypeVar(member_var))
            }
        }
    }

    fn infer_pattern_expr(
        &self,
        env: &mut Environment,
        pattern: &Pattern,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let Some(expected) = expected else {
            return Err(TypeError::Unknown(
                "Pattern is missing an expected type (from scrutinee).",
            ));
        };

        self.infer_pattern(pattern, env, expected, source_file);
        Ok(expected.clone())
    }

    fn infer_pattern(
        &self,
        pattern: &Pattern,
        env: &mut Environment,
        expected: &Ty,
        source_file: &mut SourceFile<NameResolved>,
    ) {
        log::trace!("Inferring pattern: {pattern:?}");
        match pattern {
            Pattern::LiteralInt(_) => (),
            Pattern::LiteralFloat(_) => (),
            Pattern::LiteralTrue => (),
            Pattern::LiteralFalse => (),
            Pattern::Bind(name) => {
                log::info!("inferring bind pattern: {name:?}");
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
                match expected {
                    Ty::Enum(enum_id, type_args) => {
                        // Look up the enum definition to find this variant
                        if let Some(TypeDef::Enum(enum_def)) = env.types.get(enum_id) {
                            // Find the variant by name
                            if let Some(variant) = enum_def.variants.iter().find(|v| {
                                // Match variant name (comparing the raw string)
                                v.name == *variant_name
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
                                    self.infer_node(
                                        field_pattern,
                                        env,
                                        &Some(field_ty.clone()),
                                        source_file,
                                    )
                                    .unwrap();
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

                            self.infer_node(field_pattern, env, &Some(field_ty), source_file)
                                .unwrap();
                        }
                    }
                    _ => panic!("Unhandled pattern variant: {pattern:?}"),
                }
            }
        }
    }

    fn hoist_structs(
        &self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
        _symbol_table: &mut SymbolTable,
    ) -> Result<(), TypeError> {
        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();
            let Expr::Struct(name, generics, body) = expr else {
                continue;
            };

            let Name::Resolved(symbol_id, _) = name else {
                return Err(TypeError::Unresolved);
            };

            let Some(Expr::Block(expr_ids)) = source_file.get(&body).cloned() else {
                unreachable!()
            };

            let mut methods: HashMap<String, Method> = Default::default();
            let mut properties: HashMap<String, Property> = Default::default();

            let mut type_parameters = vec![];
            for id in generics {
                match self.infer_node(&id, env, &None, source_file) {
                    Ok(ty) => type_parameters.push(ty),
                    Err(e) => source_file.diagnostics.push(Diagnostic::typing(e)),
                }
            }
            log::warn!("{type_parameters:?}");

            for expr_id in expr_ids {
                match &source_file.get(&expr_id).cloned().unwrap() {
                    Expr::Property {
                        name,
                        type_repr,
                        default_value,
                    } => {
                        let mut ty = None;
                        if let Some(type_repr) = type_repr {
                            ty = Some(self.infer_node(type_repr, env, &None, source_file)?);
                        }
                        if let Some(default_value) = default_value {
                            ty = Some(self.infer_node(default_value, env, &None, source_file)?);
                        }
                        if ty.is_none() {
                            return Err(TypeError::Unknown("No type for method"));
                        }

                        let name = match name.clone() {
                            Name::Raw(name_str) => name_str,
                            Name::Resolved(_, name_str) => name_str,
                            _ => unreachable!(),
                        };

                        properties.insert(
                            name.to_string(),
                            Property::new(name.to_string(), ty.unwrap()),
                        );
                    }
                    Expr::Func { name, .. } => {
                        let name = match name.clone() {
                            Some(Name::Raw(name_str)) => name_str,
                            Some(Name::Resolved(_, name_str)) => name_str,
                            _ => unreachable!(),
                        };

                        let ty = self.infer_node(&expr_id, env, &None, source_file)?;
                        methods.insert(name.to_string(), Method::new(name.to_string(), ty));
                    }
                    _ => return Err(TypeError::Unknown("Unhandled property")),
                }
            }

            let struct_def = StructDef::new(symbol_id, None, type_parameters, properties, methods);
            env.register_struct(struct_def);
        }

        Ok(())
    }

    fn hoist_enums(
        &self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
        symbol_table: &mut SymbolTable,
    ) -> Result<(), TypeError> {
        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();

            if let Expr::EnumDecl(Name::Resolved(enum_id, _), generics, body) = expr.clone() {
                let Some(Expr::Block(expr_ids)) = source_file.get(&body).cloned() else {
                    unreachable!()
                };

                env.start_scope();
                let mut generic_vars = vec![];
                for generic_id in generics {
                    let ty = self.infer_node(&generic_id, env, &None, source_file)?;
                    generic_vars.push(ty);
                }

                let enum_ty = Ty::Enum(enum_id, generic_vars.clone());
                let scheme = env.generalize(&enum_ty);
                log::trace!("enum scheme: {scheme:?}");
                env.declare_in_parent(enum_id, scheme);

                let mut methods: Vec<Ty> = vec![];
                let mut variants: Vec<Ty> = vec![];
                let mut variant_defs: Vec<EnumVariant> = vec![];

                // Register a placeholder
                env.register_enum(EnumDef {
                    name: Some(enum_id),
                    variants: variant_defs.clone(),
                    type_parameters: generic_vars.clone(),
                    methods: methods.clone(),
                });

                log::debug!("Generic vars: {generic_vars:?}");
                for expr_id in expr_ids.clone() {
                    let expr = source_file.get(&expr_id).cloned().unwrap();

                    if let Expr::Func { .. } = &expr {
                        let method = self.infer_node(&expr_id, env, &None, source_file)?;
                        methods.push(method);
                    }

                    if let Expr::EnumVariant(Name::Raw(name_str), values) =
                        source_file.get(&expr_id).cloned().unwrap()
                    {
                        let values: Vec<Ty> = values
                            .iter()
                            .map(|id| self.infer_node(id, env, &None, source_file).unwrap())
                            .collect();
                        let ty = Ty::EnumVariant(enum_id, values.clone());

                        let constructor_symbol = symbol_table.add(
                            &name_str,
                            crate::SymbolKind::VariantConstructor,
                            expr_id,
                        );

                        let enum_ty = Ty::Enum(enum_id, generic_vars.clone()); // e.g., Option<TypeVar_for_T>
                        let mut enum_type_unbound_vars = Vec::new();
                        let ftv_in_enum_ty = free_type_vars(&enum_ty); // Should contain TypeVar_for_T

                        for enum_tp_var_instance in &generic_vars {
                            // Iterate over [TypeVar_for_T]
                            if let Ty::TypeVar(tv_id) = enum_tp_var_instance
                                && ftv_in_enum_ty.contains(tv_id)
                            {
                                // Check if T is actually in Option<T> (it is)
                                if !enum_type_unbound_vars.contains(tv_id) {
                                    enum_type_unbound_vars.push(tv_id.clone());
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
                                id: expr_id,
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
                        log::debug!("Non-raw expr: {:?}", source_file.get(&expr_id).unwrap());
                    }
                }
                env.end_scope();

                log::debug!("Registering enum {enum_id:?}, variants: {variant_defs:?}");
                env.register_enum(EnumDef {
                    name: Some(enum_id),
                    variants: variant_defs,
                    type_parameters: generic_vars,
                    methods,
                });

                let typed_expr = TypedExpr::new(*id, expr.clone(), enum_ty.clone());
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
            let expr = source_file.get(id).unwrap().clone();

            if let Expr::Func {
                name: Some(Name::Resolved(symbol_id, _)),
                ..
            } = expr
            {
                let fn_var =
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncNameVar(symbol_id)));

                let typed_expr = TypedExpr::new(*id, expr, fn_var.clone());
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
        environment::TypeDef,
        expr::Expr,
        name::Name,
        type_checker::{Ty, TypeVarID, TypeVarKind},
    };

    fn check(code: &'static str) -> SourceFile<Typed> {
        crate::check(code).unwrap()
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

        let Ty::Func(params, return_type, _) = checker.type_for(root_id) else {
            panic!("didnt get a func, got: {:#?}", checker.type_for(root_id));
        };

        let param_type = params[0].clone();

        assert_eq!(return_type, param_type.into());
        assert_eq!(
            *return_type,
            Ty::TypeVar(TypeVarID(3, TypeVarKind::FuncParam))
        );

        // The second root-expr is the *use* of `sup`.
        let Ty::Func(params2, return_type2, _) = checker.type_for(checker.root_ids()[1]) else {
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
        let Ty::Func(params, return_type, _) = checker.type_for(root_id) else {
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
        let Ty::Func(params, return_type, _) = checker.type_for(root_id) else {
            panic!(
                "expected `applyTwice` to be a function, got: {:?}",
                checker.type_for(root_id)
            );
        };

        // applyTwice should have exactly 2 parameters
        assert_eq!(params.len(), 2);

        // f : A -> A
        match &params[0] {
            Ty::Func(arg_tys, ret_ty, _) => {
                assert_eq!(arg_tys.len(), 1);
                // the return of f must be the same type as x
                assert_eq!(**ret_ty, params[1].clone());
            }
            other => panic!("`f` should be a function, got {other:?}"),
        }

        // the overall return type of applyTwice is the same as x
        assert_eq!(return_type, params[1].clone().into());
    }

    #[test]
    fn checks_call_with_generics() {
        let checked = check(
            "
        func fizz<T>(ty: T) { T }

        fizz<Int>(123)
        fizz<Bool>(true)
        ",
        );

        assert_eq!(checked.type_for(checked.root_ids()[1]), Ty::Int);
        assert_eq!(checked.type_for(checked.root_ids()[2]), Ty::Bool);
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
        let Ty::Func(params, return_type, _) = checker.type_for(root_id) else {
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
        let Ty::Func(f_args, f_ret, _) = f_ty.clone() else {
            panic!("did not get func: {f_ty:?}");
        };
        assert_eq!(f_args.len(), 1);

        // g : A -> B
        let Ty::Func(g_args, g_ret, _) = g_ty.clone() else {
            panic!("did not get func")
        };

        assert_eq!(g_args.len(), 1);

        // g's return type (B) must match f's argument type
        assert_eq!(*g_ret, f_args[0].clone());

        // the inner function's return (and thus compose's return) is f's return type C
        let Ty::Closure {
            func: box Ty::Func(inner_params, inner_ret, _),
            ..
        } = *return_type
        else {
            panic!("expected `compose` to return a closure, got {return_type:?}",);
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
        let Ty::Closure {
            func: box Ty::Func(params, ret, _),
            ..
        } = ty
        else {
            panic!()
        };
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
            Ty::Closure {
                func: box Ty::Func(params, ret, _),
                ..
            } => {
                assert_eq!(params.len(), 1);
                // both even and odd must have the same input and output type
                assert_eq!(*ret, Ty::Int);
                assert_eq!(params[0].clone(), Ty::Int);
            }
            other => panic!("expected a function, got {other:?}"),
        }
    }

    #[test]
    fn infers_let_with_enum_case() {
        let checked = check(
            "
        enum Maybe<T> {
          case definitely(T), nope
        }

        let maybe = Maybe.definitely(123)
        maybe
        ",
        );

        assert_eq!(
            checked.type_for(checked.root_ids()[2]),
            Ty::Enum(SymbolID::typed(1), vec![Ty::Int]),
        );
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
            Ty::Enum(SymbolID::typed(1), vec![])
        );

        // Check the variants
        assert_eq!(
            checker.type_for(0),
            Ty::EnumVariant(SymbolID::typed(1), vec![])
        );
        assert_eq!(
            checker.type_for(1),
            Ty::EnumVariant(SymbolID::typed(1), vec![])
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
            Ty::Enum(SymbolID::typed(1), vec![])
        );

        // Check variant types
        assert_eq!(
            checker.type_for(1),
            Ty::EnumVariant(SymbolID::typed(1), vec![Ty::Int]),
        );
        assert_eq!(
            checker.type_for(2),
            Ty::EnumVariant(SymbolID::typed(1), vec![])
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
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics.len(), 1);
                // Should be a type variable for T
                assert!(matches!(generics[0], Ty::TypeVar(_)));
            }
            _ => panic!("Expected generic enum type, got {enum_ty:?}"),
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
        assert_eq!(call_result, Ty::Enum(SymbolID::typed(1), vec![]));
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
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Option<Int>, got {call1:?}"),
        }

        // Second call should be Option<Float>
        let call2 = checker.type_for(checker.root_ids()[2]);
        match call2 {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics, vec![Ty::Float]);
            }
            _ => panic!("Expected Option<Float>, got {call2:?}"),
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
                assert_eq!(symbol_id, SymbolID::typed(3)); // Result enum
                assert_eq!(generics.len(), 2);

                // First generic should be Option<Int>
                match &generics[0] {
                    Ty::Enum(opt_id, opt_generics) => {
                        assert_eq!(*opt_id, SymbolID::typed(1)); // Option enum
                        assert_eq!(opt_generics, &vec![Ty::Int]);
                    }
                    _ => panic!("Expected Option<Int> as first generic"),
                }
            }
            _ => panic!("Expected Result type, got {result_ty:?}"),
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
            Ty::Func(params, ret, _) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], Ty::Enum(SymbolID::typed(1), vec![])); // Bool
                assert_eq!(*ret, Ty::Int);
            }
            _ => panic!("Expected function type, got {func_ty:?}"),
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
            Ty::Func(params, ret, _) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], Ty::Enum(SymbolID::typed(1), vec![Ty::Int])); // Option<Int>
                assert_eq!(*ret, Ty::Int);
            }
            _ => panic!("Expected function type, got {func_ty:?}"),
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
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics.len(), 1);
            }
            _ => panic!("Expected List<T> type, got {enum_ty:?}"),
        }

        let Some(Expr::EnumDecl(_, _, body)) = checker.roots()[0] else {
            panic!("did not get enum decl");
        };

        assert_eq!(*body, 6);

        let Some(Expr::Block(exprs)) = checker.get(&6) else {
            panic!("did not get body");
        };

        assert_eq!(exprs[0], 4);

        // Check cons variant has recursive structure: T, List<T>
        let cons_variant = checker.type_for(4);
        match cons_variant {
            Ty::EnumVariant(enum_id, field_types) => {
                assert_eq!(enum_id, SymbolID::typed(1));
                assert_eq!(field_types.len(), 2);
                // Second field should be List<T> (recursive reference)
                match &field_types[1] {
                    Ty::Enum(list_id, _) => assert_eq!(*list_id, SymbolID::typed(1)),
                    _ => panic!("Expected recursive List type"),
                }
            }
            _ => panic!("Expected cons variant type, got: {cons_variant:?}"),
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
        assert_eq!(call_result, Ty::Enum(SymbolID::typed(1), vec![])); // Bool
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
        assert_eq!(call_result, Ty::Enum(SymbolID::typed(1), vec![Ty::Int])); // Option<Int>
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
            Ty::Func(params, ret, _) => {
                // Input: Either<Int, Float>
                assert_eq!(
                    params[0],
                    Ty::Enum(SymbolID::typed(1), vec![Ty::Int, Ty::Float])
                );
                // Output: Either<Float, Int>
                assert_eq!(*ret, Ty::Enum(SymbolID::typed(1), vec![Ty::Float, Ty::Int]));
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
        assert_eq!(x_ty, Ty::Int.optional());
        match x_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::OPTIONAL); // Optional's ID
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Optional<Int>, got {x_ty:?}"),
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
        let Ty::Func(args, ret, _) = checker.type_for(checker.root_ids()[0]) else {
            panic!("did not get func")
        };

        assert_eq!(
            args[0],
            Ty::Enum(
                SymbolID::OPTIONAL,
                vec![Ty::TypeVar(TypeVarID(
                    6,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::typed(3), "T".into()))
                ))]
            )
        );
        assert_eq!(
            args[1],
            Ty::Func(
                vec![Ty::TypeVar(TypeVarID(
                    6,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::typed(3), "T".into()))
                ))],
                Ty::TypeVar(TypeVarID(
                    5,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::typed(2), "U".into()))
                ))
                .into(),
                vec![]
            )
        );
        assert_eq!(
            ret,
            Ty::Enum(
                SymbolID(1),
                vec![Ty::TypeVar(TypeVarID(
                    5,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID(6), "U".into()))
                ))]
            )
            .into()
        );

        let call_result = checker.type_for(checker.root_ids()[1]);
        match call_result {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(-3)); // Optional's ID
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Optional<Int>, got {call_result:?}"),
        }
    }

    #[test]
    fn checks_self() {
        let checked = check(
            "enum Fizz {
            func buzz() {
                self
            }

            func foo() {
                123
            }
        }",
        );

        assert_eq!(
            checked.typed_roots()[0].ty,
            Ty::Enum(SymbolID::typed(1), vec![])
        );
        let Some(TypeDef::Enum(enum_def)) = checked.type_def(&SymbolID::typed(1)) else {
            panic!();
        };
        assert_eq!(enum_def.methods.len(), 2);
        assert_eq!(
            enum_def.methods[0],
            Ty::Func(
                vec![],
                Box::new(Ty::Enum(SymbolID::typed(1), vec![])),
                vec![]
            )
        );
        assert_eq!(
            enum_def.methods[1],
            Ty::Func(vec![], Box::new(Ty::Int), vec![])
        );
    }

    #[test]
    fn checks_closure() {
        let checked = check(
            "
        let x = 1 
        func add(y) {
            x + y
        }
        ",
        );

        assert_eq!(
            checked.type_for(8),
            Ty::Closure {
                func: Ty::Func(vec![Ty::Int], Ty::Int.into(), vec![]).into(),
                captures: vec![Ty::Int]
            }
        );
    }

    #[test]
    fn checks_array() {
        let checked = check(
            "
            [1,2,3]
        ",
        );

        assert_eq!(
            checked.type_for(checked.root_ids()[0]),
            Ty::Array(Box::new(Ty::Int))
        );
    }

    #[test]
    fn checks_array_builtin() {
        let checked = check("func c(a: Array<Int>) { a }");
        assert_eq!(checked.type_for(1), Ty::Array(Box::new(Ty::Int)));
    }

    #[test]
    fn checks_arrays_with_polymorphism() {
        let checked = check(
            "
        func identity(a) { a }
        identity([1,2,3])
        identity([1.0, 2.0, 3.0])
        ",
        );

        assert_eq!(
            checked.type_for(checked.root_ids()[1]),
            Ty::Array(Ty::Int.into())
        );
        assert_eq!(
            checked.type_for(checked.root_ids()[2]),
            Ty::Array(Ty::Float.into())
        );
    }
}

#[cfg(test)]
mod pending {
    use super::Ty;
    use crate::type_checker::TypeError;

    fn check_err(code: &'static str) -> Result<Ty, TypeError> {
        let inferred = crate::check(code)?;
        Ok(inferred.type_for(inferred.root_ids()[0]))
    }

    fn check(code: &'static str) -> Ty {
        check_err(code).unwrap()
    }

    // #[test]
    // fn checks_match_exhaustiveness_error() {
    //     // This should fail type checking due to non-exhaustive match
    //     let result = std::panic::catch_unwind(|| {
    //         check(
    //             "
    //             enum Bool {
    //                 case yes, no
    //             }
    //             func test(b: Bool) -> Int {
    //                 match b {
    //                     .yes -> 1
    //                 }
    //             }
    //             ",
    //         )
    //     });

    //     // Should panic or return error - depends on your error handling
    //     assert!(result.is_err());
    // }

    #[test]
    fn checks_literal_true() {
        assert_eq!(check("true"), Ty::Bool);
    }

    #[test]
    fn checks_literal_false() {
        assert_eq!(check("false"), Ty::Bool);
    }

    #[test]
    fn checks_if_expression() {
        assert_eq!(check("if true { 1 } else { 0 }"), Ty::Int);
    }

    #[test]
    fn checks_if_expression_without_else() {
        assert_eq!(check("if true { 1 }"), Ty::Int.optional());
    }

    #[test]
    fn checks_if_expression_with_non_bool_condition() {
        assert!(check_err("if 123 { 1 }").is_err());
    }

    #[test]
    fn checks_loop_expression() {
        assert_eq!(check("loop { 1 }"), Ty::Void);
    }

    #[test]
    fn checks_loop_expression_with_condition() {
        assert_eq!(check("loop true { 1 }"), Ty::Void);
    }

    #[test]
    fn checks_loop_expression_with_invalid_condition() {
        assert!(check_err("loop 1.2 { 1 }").is_err());
    }

    #[test]
    fn checks_tuple_expression() {
        assert_eq!(check("(1, true)"), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn checks_unit_tuple_expression() {
        assert_eq!(check("()"), Ty::Tuple(vec![]));
    }

    #[test]
    fn checks_tuple_expectations() {
        assert!(
            check_err(
                "
            let my_tuple: (Int, Bool) = (42, 10)
            ",
            )
            .is_err()
        );
    }

    #[test]
    fn checks_grouping_expression() {
        assert_eq!(check("(1)"), Ty::Int);
    }

    #[test]
    fn checks_unary_expression() {
        check("-1"); // Assuming '-' is a unary op
    }

    #[test]
    fn checks_binary_expression() {
        check("1 + 2");
    }

    #[test]
    fn checks_void_expr() {
        assert_eq!(
            check(
                "func foo() {
            return
        }()"
            ),
            Ty::Void
        );
    }

    #[test]
    fn checks_return_err() {
        assert!(
            check_err(
                "func foo() -> Int {
            return
        }()"
            )
            .is_err(),
        );
    }

    #[test]
    fn checks_return_infer() {
        assert_eq!(
            check(
                "func foo(x) {
            return x
            123
        }"
            ),
            Ty::Func(vec![Ty::Int], Ty::Int.into(), vec![])
        );
    }

    #[test]
    fn checks_return_expr() {
        assert_eq!(
            check(
                "func foo() {
            return 123
        }()"
            ),
            Ty::Int
        );
    }

    #[test]
    fn checks_pattern_literal_int_in_match() {
        check(
            "
            enum MyEnum {
                case val(Int)
            }
            func test(e: MyEnum) {
                match e {
                    .val(1) -> 0
                }
            }
        ",
        );
    }

    #[test]
    #[should_panic]
    fn checks_pattern_wildcard_in_match() {
        check(
            "
            enum MyEnum { case Val(Int) }
            func test(e: MyEnum) {
                match e {
                    _ -> 0 // Pattern::Wildcard
                }
            }
        ",
        );
    }
}
