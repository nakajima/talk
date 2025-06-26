use std::{collections::HashMap, hash::Hash};

use crate::{
    NameResolved, SymbolID, SymbolTable, Typed,
    constraint_solver::{Constraint, ConstraintSolver},
    diagnostic::Diagnostic,
    environment::{EnumVariant, Method, Property, RawEnumVariant, RawMethod, StructDef},
    expr::{Expr, Pattern},
    name::Name,
    name_resolver::NameResolverError,
    parser::ExprID,
    source_file::SourceFile,
    synthesis::synthesize_inits,
    token_kind::TokenKind,
    ty::Ty,
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
    CanonicalTypeParameter(String),
    Placeholder(String),
    Unbound,
}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum TypeError {
    Unresolved(String),
    NameResolution(NameResolverError),
    UnknownEnum(Name),
    UnknownVariant(Name),
    Unknown(String),
    UnexpectedType(Ty, Ty),
    Mismatch(Ty, Ty),
    Handled, // If we've already reported it
    OccursConflict,
}

impl TypeError {
    pub fn message(&self) -> String {
        match self {
            Self::Unresolved(name) => format!("Unresolved name: {name}"),
            Self::NameResolution(e) => e.message(),
            Self::UnknownEnum(name) => format!("No enum named {}", name.name_str()),
            Self::UnknownVariant(name) => format!("No case named {}", name.name_str()),
            Self::Unknown(err) => format!("Unknown error: {err}"),
            Self::UnexpectedType(actual, expected) => {
                format!("Unexpected type: {expected}, expected: {actual}")
            }
            Self::Mismatch(expected, actual) => {
                format!("Unexpected type: {expected}, expected: {actual}")
            }
            Self::Handled => unreachable!("Handled errors should not be displayed"),
            Self::OccursConflict => "Recursive types are not supported".to_string(),
        }
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
        self.infer_without_prelude(env, source_file, symbol_table)
    }

    pub fn predeclare(
        &self,
        items: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
        symbol_table: &mut SymbolTable,
    ) -> Result<(), TypeError> {
        if let Err((id, err)) = self.predeclare_structs(items, env, source_file, symbol_table) {
            source_file.diagnostics.insert(Diagnostic::typing(id, err));
        }

        if let Err((id, err)) = self.predeclare_enums(items, env, source_file, symbol_table) {
            source_file.diagnostics.insert(Diagnostic::typing(id, err));
        }

        self.predeclare_functions(items, env, source_file)?;

        Ok(())
    }

    pub fn infer_without_prelude(
        &self,
        env: &mut Environment,
        mut source_file: SourceFile<NameResolved>,
        symbol_table: &mut SymbolTable,
    ) -> SourceFile<Typed> {
        let root_ids = source_file.root_ids();
        synthesize_inits(&mut source_file, symbol_table, env);

        // Just define names for all of the funcs, structs and enums
        self.predeclare(&root_ids, env, &mut source_file, symbol_table)
            .ok();

        let mut typed_roots = vec![];
        for id in &root_ids {
            match self.infer_node(id, env, &None, &mut source_file) {
                Ok(_ty) => typed_roots.push(env.typed_exprs.get(id).unwrap().clone()),
                Err(e) => {
                    source_file.diagnostics.insert(Diagnostic::typing(*id, e));
                }
            }
        }

        source_file.to_typed()
    }

    pub fn infer_nodes(
        &self,
        ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Vec<Ty>, TypeError> {
        let mut result = vec![];
        for id in ids {
            result.push(self.infer_node(id, env, &None, source_file)?);
        }
        Ok(result)
    }

    pub fn infer_node(
        &self,
        id: &ExprID,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let expr = source_file.get(id).unwrap().clone();
        let mut ty = match &expr {
            Expr::LiteralTrue | Expr::LiteralFalse => checked_expected(expected, Ty::Bool),
            Expr::Loop(cond, body) => self.infer_loop(cond, body, env, source_file),
            Expr::If(condition, consequence, alternative) => {
                let ty = self.infer_if(condition, consequence, alternative, env, source_file);
                if let Ok(ty) = &ty {
                    checked_expected(expected, ty.clone())?;
                }

                ty
            }
            Expr::Call {
                callee,
                type_args,
                args,
            } => self.infer_call(id, env, callee, type_args, args, expected, source_file),
            Expr::LiteralInt(_) => checked_expected(expected, Ty::Int),
            Expr::LiteralFloat(_) => checked_expected(expected, Ty::Float),
            Expr::Assignment(lhs, rhs) => self.infer_assignment(env, lhs, rhs, source_file),
            Expr::TypeRepr(name, generics, is_type_parameter) => {
                self.infer_type_repr(id, env, name, generics, is_type_parameter, source_file)
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
                self.infer_let(env, *symbol_id, rhs, expected, source_file)
            }
            Expr::Variable(Name::Resolved(symbol_id, name), _) => {
                self.infer_variable(id, env, *symbol_id, name)
            }
            Expr::Parameter(Name::Resolved(symbol_id, _), param_ty) => {
                self.infer_parameter(symbol_id, param_ty, env, source_file)
            }
            Expr::Tuple(types) => self.infer_tuple(types, env, source_file),
            Expr::Unary(_token_kind, rhs) => self.infer_unary(rhs, expected, env, source_file),
            Expr::Binary(lhs, op, rhs) => {
                self.infer_binary(id, lhs, rhs, op, expected, env, source_file)
            }
            Expr::Block(_) => self.infer_block(id, env, expected, source_file),
            Expr::EnumDecl(Name::Resolved(symbol_id, _), _generics, body) => {
                self.infer_enum_decl(symbol_id, body, env, source_file)
            }
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
            Expr::Variable(Name::Raw(name_str), _) => Err(TypeError::Unresolved(name_str.clone())),
            Expr::Variable(Name::_Self(sym), _) => Ok(env.lookup_symbol(sym).unwrap().ty.clone()),
            Expr::Return(rhs) => self.infer_return(rhs, env, expected, source_file),
            Expr::LiteralArray(items) => self.infer_array(items, env, expected, source_file),
            Expr::Struct(name, generics, body) => {
                self.infer_struct(name, generics, body, env, expected, source_file)
            }
            Expr::CallArg { value, .. } => self.infer_node(value, env, expected, source_file),
            Expr::Init(Some(struct_id), func_id) => {
                self.infer_init(struct_id, func_id, env, source_file)
            }
            Expr::Break => Ok(Ty::Void),
            _ => Err(TypeError::Unknown(format!(
                "Don't know how to type check {expr:?}"
            ))),
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
            Err(e) => {
                source_file
                    .diagnostics
                    .insert(Diagnostic::typing(*id, e.clone()));
                ty = Err(TypeError::Handled)
            }
        }

        ty
    }

    fn infer_enum_decl(
        &self,
        enum_id: &SymbolID,
        body: &ExprID,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        // 1. Look up the EnumDef that predeclareing created.
        let enum_def = env.lookup_enum(enum_id).unwrap().clone();
        let enum_scheme = env.lookup_symbol(enum_id).unwrap().clone();

        env.start_scope();
        env.declare(*enum_id, enum_scheme.clone());

        let mut inferred_methods = HashMap::new();
        for (name, raw_method) in enum_def.raw_methods.iter() {
            let method_ty = self.infer_node(&raw_method.expr_id, env, &None, source_file)?;
            inferred_methods.insert(name.clone(), Method::new(name.clone(), method_ty));
        }

        let mut inferred_variants = vec![];
        for variant in enum_def.raw_variants {
            let variant_values = self.infer_nodes(&variant.values, env, source_file)?;
            inferred_variants.push(EnumVariant {
                name: variant.name,
                values: variant_values,
            });
        }

        let enum_def_mut = env.lookup_enum_mut(enum_id).unwrap();
        enum_def_mut.methods = inferred_methods;
        enum_def_mut.variants = inferred_variants;

        let scheme = env.lookup_symbol(enum_id)?;
        Ok(scheme.ty.clone())
    }

    fn infer_parameter(
        &self,
        symbol_id: &SymbolID,
        param_ty: &Option<ExprID>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let param_ty = if let Some(param_ty) = &param_ty {
            self.infer_node(param_ty, env, &None, source_file)?
        } else {
            Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncParam))
        };

        // Parameters are monomorphic inside the function body
        let scheme = Scheme::new(param_ty.clone(), vec![]);
        log::info!("declared parameter scheme: {symbol_id:?} {scheme:?}");
        env.declare(*symbol_id, scheme);

        Ok(param_ty)
    }

    fn infer_init(
        &self,
        struct_id: &SymbolID,
        func_id: &ExprID,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let inferred = self.infer_node(func_id, env, &None, source_file)?;
        let params = match inferred {
            Ty::Func(params, _, _) => params,
            Ty::Closure {
                func: box Ty::Func(params, _, _),
                ..
            } => params,
            _ => {
                return Err(TypeError::Unknown(format!(
                    "Did not get init func, got: {inferred:?}"
                )));
            }
        };

        Ok(Ty::Init(*struct_id, params))
    }

    fn infer_struct(
        &self,
        name: &Name,
        generics: &[ExprID],
        body: &ExprID,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let mut inferred_generics: Vec<Ty> = vec![];
        for generic in generics {
            inferred_generics.push(
                self.infer_node(generic, env, expected, source_file)?
                    .clone(),
            );
        }

        let Name::Resolved(symbol_id, _) = name else {
            return Err(TypeError::Unresolved(name.name_str()));
        };

        let Some(Expr::Block(items)) = source_file.get(body).cloned() else {
            unreachable!()
        };

        for item in items {
            match source_file.get(&item) {
                Some(Expr::Property { .. }) => todo!(),
                _ => {
                    self.infer_node(&item, env, expected, source_file)?;
                }
            }
        }

        Ok(Ty::Struct(*symbol_id, inferred_generics))
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

        Ok(Ty::Struct(SymbolID::ARRAY, vec![ty]))
    }

    fn infer_return(
        &self,
        rhs: &Option<ExprID>,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        if let Some(rhs_id) = rhs {
            let inferred_rhs_ty = self.infer_node(rhs_id, env, expected, source_file)?;
            Ok(inferred_rhs_ty)
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
        id: &ExprID,
        env: &mut Environment,
        callee: &ExprID,
        type_args: &[ExprID],
        args: &[ExprID],
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let mut ret_var = if let Some(expected) = expected {
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
            let ty = self.infer_node(arg, env, &None, source_file)?;
            arg_tys.push(ty);
        }

        match source_file.get(callee).cloned() {
            // Handle struct initialization
            Some(Expr::Variable(Name::Resolved(symbol_id, name_str), _))
                if env.is_struct_symbol(&symbol_id) =>
            {
                ret_var = env.ty_for_symbol(id, name_str, &symbol_id);
            }
            _ => {
                let callee_ty = self.infer_node(callee, env, &None, source_file)?;
                // let callee_ty = env.instantiate(&env.generalize(&callee_ty));
                let expected_callee_ty =
                    Ty::Func(arg_tys, Box::new(ret_var.clone()), inferred_type_args);
                env.constrain_equality(*callee, callee_ty.clone(), expected_callee_ty);
            }
        };

        Ok(ret_var)
    }

    fn infer_assignment(
        &self,
        env: &mut Environment,
        lhs: &ExprID,
        rhs: &ExprID,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let rhs_ty = self.infer_node(rhs, env, &None, source_file)?;

        // Expect lhs to be the same as rhs
        let lhs_ty = self.infer_node(lhs, env, &Some(rhs_ty.clone()), source_file)?;

        env.constrain_equality(*rhs, rhs_ty.clone(), lhs_ty);

        Ok(rhs_ty)
    }

    fn infer_type_repr(
        &self,
        id: &ExprID,
        env: &mut Environment,
        name: &Name,
        generics: &[ExprID],
        is_type_parameter: &bool,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        if *is_type_parameter {
            return Ok(Ty::TypeVar(
                env.new_type_variable(TypeVarKind::Placeholder(name.name_str())),
            ));
        }

        let symbol_id = name.try_symbol_id();
        let base_ty_placeholder = env.ty_for_symbol(id, name.name_str(), &symbol_id);

        // If there are no generic arguments (`let x: Int`), we are done.
        if generics.is_empty() {
            return Ok(base_ty_placeholder);
        }

        let mut arg_ty_placeholders = Vec::new();
        for generic_id in generics {
            // Recursively get arg_ty
            let arg_ty = self.infer_node(generic_id, env, &None, source_file)?;
            arg_ty_placeholders.push(arg_ty);
        }

        // 3. Create a new placeholder for the final, specialized type (Array<Int>).
        let result_placeholder = Ty::TypeVar(env.new_type_variable(TypeVarKind::Blank));

        // 4. Generate the GenericApplication constraint.
        // env.constraints.push(Constraint::GenericApplication {
        //     generic_ty: base_ty_placeholder,
        //     arg_tys: arg_ty_placeholders,
        //     result_ty: result_placeholder.clone(),
        // });

        // 5. Return the placeholder for the final result.
        Ok(result_placeholder)
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
        _expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        env.start_scope();

        let predeclared_ty = if let Some(Name::Resolved(symbol_id, _)) = name
            && let Ok(scheme) = env.lookup_symbol(symbol_id).cloned()
        {
            let ty = env.instantiate(&scheme);
            env.declare(*symbol_id, scheme);
            Some(ty)
        } else {
            None
        };

        let mut inferred_generics = vec![];
        for generic in generics {
            if let Some(Expr::TypeRepr(Name::Resolved(symbol_id, _), _, _)) =
                source_file.get(generic).cloned()
            {
                let ty = self.infer_node(generic, env, &None, source_file)?;
                inferred_generics.push(ty.clone());
                let scheme = Scheme::new(ty.clone(), vec![]);
                env.declare(symbol_id, scheme);
            } else {
                return Err(TypeError::Unresolved(
                    "could not resolve generic symbol".into(),
                ));
            }
        }

        let expected_body_ty = if let Some(ret) = ret {
            Some(self.infer_node(ret, env, &None, source_file)?)
        } else {
            None
        };

        let mut param_vars: Vec<Ty> = vec![];
        for param in params.iter() {
            let param_ty = self.infer_node(param, env, &None, source_file)?;
            param_vars.push(param_ty);
        }

        let body_ty = self.infer_node(body, env, &expected_body_ty, source_file)?;

        if let Some(ret_type) = expected_body_ty {
            env.constrain_equality(ret.unwrap(), body_ty.clone(), ret_type);
        }

        env.end_scope();

        let func_ty = Ty::Func(param_vars.clone(), Box::new(body_ty), inferred_generics);
        let inferred_ty = if captures.is_empty() {
            func_ty
        } else {
            Ty::Closure {
                func: func_ty.into(),
                captures: captures.to_vec(),
            }
        };

        if let Some(predeclared_ty) = predeclared_ty {
            env.constrain_equality(*id, predeclared_ty, inferred_ty.clone());
        }

        if let Some(Name::Resolved(symbol_id, _)) = name {
            // Create the final, polymorphic scheme.
            let scheme = env.generalize(&inferred_ty);

            // Update the declaration in the environment with the *real*, polymorphic scheme.
            env.declare(*symbol_id, scheme);
        }

        Ok(inferred_ty)
    }

    fn infer_let(
        &self,
        env: &mut Environment,
        symbol_id: SymbolID,
        rhs: &Option<ExprID>,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let rhs_ty = if let Some(rhs) = rhs {
            self.infer_node(rhs, env, &None, source_file)?
        } else if let Some(expected) = expected {
            expected.clone()
        } else {
            Ty::TypeVar(env.new_type_variable(TypeVarKind::Let))
        };

        let scheme = Scheme::new(rhs_ty.clone(), vec![]);
        env.declare(symbol_id, scheme);

        Ok(rhs_ty)
    }

    fn infer_variable(
        &self,
        id: &ExprID,
        env: &mut Environment,
        symbol_id: SymbolID,
        name: &str,
    ) -> Result<Ty, TypeError> {
        let ty = env.ty_for_symbol(id, name.to_string(), &symbol_id);
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
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let Some(Expr::Block(items)) = source_file.get(id).cloned() else {
            return Err(TypeError::Unknown("Didn't get block".into()));
        };

        env.start_scope();
        self.predeclare_functions(&items, env, source_file)?;

        let mut block_return_ty = None;

        let mut ret_tys = vec![];

        for (i, item_id) in items.iter().enumerate() {
            let item_expr = source_file.get(item_id).cloned().unwrap();

            if let Expr::Return(_) = item_expr {
                // Explicit returns count as a return value (duh)
                let ty = self.infer_node(item_id, env, expected, source_file)?;
                ret_tys.push(ty.clone());
                block_return_ty = Some(ty);
            } else if i == items.len() - 1 {
                // The last item counts as a return value
                let ty = self.infer_node(item_id, env, &expected, source_file)?;
                block_return_ty = Some(ty);

                // If we have any explicit returns, we need to constrain equality of this with them
                for ret_ty in &ret_tys {
                    env.constrain_equality(
                        *item_id,
                        block_return_ty.clone().unwrap(),
                        ret_ty.clone(),
                    );
                }
            } else {
                block_return_ty = Some(self.infer_node(item_id, env, &None, source_file)?);
            }
        }

        env.end_scope();

        Ok(block_return_ty.unwrap())
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

                let member_var = match receiver_ty {
                    Ty::Struct(struct_id, _) => env
                        .lookup_struct(&struct_id)
                        .and_then(|s| s.member_ty(member_name))
                        .cloned(),
                    _ => None,
                }
                .clone();

                let member_var =
                    member_var.unwrap_or(Ty::TypeVar(env.new_type_variable(TypeVarKind::Member)));

                // Add a constraint that links the receiver type to the member
                env.constrain_member(
                    *id,
                    receiver_ty,
                    member_name.to_string(),
                    member_var.clone(),
                );

                Ok(member_var.clone())
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
                "Pattern is missing an expected type (from scrutinee).".into(),
            ));
        };

        self.infer_pattern(pattern, env, expected, source_file)?;
        Ok(expected.clone())
    }

    fn infer_pattern(
        &self,
        pattern: &Pattern,
        env: &mut Environment,
        expected: &Ty,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), TypeError> {
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
                    let scheme = Scheme {
                        ty: expected.clone(),
                        unbound_vars: vec![],
                    };
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
                    Ty::Enum(_enum_id, _type_args) => {
                        let mut field_tys = vec![];
                        for field_pattern_id in fields {
                            // Create a fresh var for each field
                            let field_ty =
                                Ty::TypeVar(env.new_type_variable(TypeVarKind::VariantValue));
                            field_tys.push(field_ty.clone());

                            // Recursively infer the sub-pattern, telling it to bind to our new var
                            self.infer_node(field_pattern_id, env, &Some(field_ty), source_file)?;
                        }

                        env.constraints.push(Constraint::VariantMatch {
                            scrutinee_ty: expected.clone(), // The type of the value being matched (the `expected` type)
                            variant_name: variant_name.clone(),
                            field_tys,
                        });
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

        Ok(())
    }

    fn predeclare_structs(
        &self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
        _symbol_table: &mut SymbolTable,
    ) -> Result<(), (ExprID, TypeError)> {
        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();
            let Expr::Struct(name, generics, body) = expr else {
                continue;
            };

            let Name::Resolved(symbol_id, name_str) = name else {
                return Err((*id, TypeError::Unresolved(name.name_str())));
            };

            let mut methods: HashMap<String, RawMethod> = Default::default();
            let mut properties: Vec<Property> = Default::default();
            let mut type_parameters = vec![];
            let mut initializers = vec![];

            for id in generics {
                let Some(Expr::TypeRepr(Name::Resolved(symbol_id, name_str), _, _)) =
                    source_file.get(&id)
                else {
                    return Err((
                        id,
                        TypeError::Unresolved("did not resolve type parameter for struct".into()),
                    ));
                };

                type_parameters.push(Ty::TypeVar(env.new_type_variable(
                    TypeVarKind::CanonicalTypeParameter(format!("{}{}", name_str, symbol_id.0)),
                )));
            }

            // The type of the struct, using the canonical placeholders.
            let struct_ty = Ty::Struct(symbol_id, type_parameters.clone());

            // The unbound vars of this type ARE its canonical placeholders.
            let unbound_vars = type_parameters
                .iter()
                .filter_map(|ty| match ty {
                    Ty::TypeVar(tv) => Some(tv.clone()),
                    _ => None,
                })
                .collect();

            let scheme = Scheme::new(struct_ty, unbound_vars);
            env.declare(symbol_id, scheme);

            let Some(Expr::Block(body_ids)) = source_file.get(&body).cloned() else {
                unreachable!()
            };

            for body_id in body_ids {
                let expr = &source_file.get(&body_id).cloned().unwrap();
                match &expr {
                    Expr::Property { name, .. } => {
                        properties.push(Property {
                            name: name.name_str(),
                            symbol: expr.symbol_id().unwrap(),
                            expr_id: body_id,
                        });
                    }
                    Expr::Init(_, _) => {
                        initializers.push(body_id);
                    }
                    Expr::Func { name, .. } => {
                        let name = match name.clone() {
                            Some(Name::Raw(name_str)) => name_str,
                            Some(Name::Resolved(_, name_str)) => name_str,
                            _ => unreachable!(),
                        };

                        methods.insert(
                            name.to_string(),
                            RawMethod {
                                name: name.to_string(),
                                expr_id: body_id,
                            },
                        );
                    }
                    _ => {
                        return {
                            log::error!("Unhandled property: {:?}", source_file.get(&body_id));
                            Err((
                                *id,
                                TypeError::Unknown(format!(
                                    "Unhandled property: {:?}",
                                    source_file.get(&body_id)
                                )),
                            ))
                        };
                    }
                }
            }

            let struct_def = StructDef::new(
                symbol_id,
                name_str,
                type_parameters.clone(),
                properties,
                methods,
                initializers
                    .iter()
                    .map(|i| (source_file.path.clone(), *i))
                    .collect(),
            );

            // Register updated definition
            env.register_struct(struct_def);
        }

        Ok(())
    }

    fn predeclare_enums(
        &self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
        _symbol_table: &mut SymbolTable,
    ) -> Result<(), (ExprID, TypeError)> {
        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();

            let Expr::EnumDecl(Name::Resolved(enum_id, _), generics, body) = expr.clone() else {
                continue;
            };

            let Some(Expr::Block(expr_ids)) = source_file.get(&body).cloned() else {
                unreachable!()
            };

            let mut generic_vars = vec![];
            for id in generics {
                let Some(Expr::TypeRepr(Name::Resolved(symbol_id, name_str), _, _)) =
                    source_file.get(&id)
                else {
                    return Err((
                        id,
                        TypeError::Unresolved("did not resolve type parameter for struct".into()),
                    ));
                };

                generic_vars.push(Ty::TypeVar(env.new_type_variable(
                    TypeVarKind::CanonicalTypeParameter(format!("{}{}", name_str, symbol_id.0)),
                )));
            }

            let enum_ty = Ty::Enum(enum_id, generic_vars.clone());
            let unbound_vars = generic_vars
                .iter()
                .filter_map(|ty| match ty {
                    Ty::TypeVar(tv) => Some(tv.clone()),
                    _ => None,
                })
                .collect();

            let scheme = Scheme::new(enum_ty, unbound_vars);
            env.declare(enum_id, scheme);

            let mut raw_methods: HashMap<String, RawMethod> = Default::default();
            let mut variant_defs: Vec<RawEnumVariant> = vec![];

            for expr_id in expr_ids.clone() {
                let expr = source_file.get(&expr_id).cloned().unwrap();

                if let Expr::Func {
                    name: Some(Name::Resolved(_, name_str)),
                    ..
                } = &expr
                {
                    raw_methods.insert(
                        name_str.clone(),
                        RawMethod::new(name_str.to_string(), expr_id),
                    );
                }

                if let Expr::EnumVariant(Name::Raw(name_str), values) =
                    source_file.get(&expr_id).cloned().unwrap()
                {
                    variant_defs.push(RawEnumVariant {
                        name: name_str,
                        values,
                    });
                } else {
                    log::debug!("Non-raw expr: {:?}", source_file.get(&expr_id).unwrap());
                }
            }

            env.register_enum(EnumDef {
                name: Some(enum_id),
                raw_variants: variant_defs,
                variants: Default::default(),
                type_parameters: generic_vars,
                raw_methods,
                methods: Default::default(),
            });
        }

        Ok(())
    }

    fn predeclare_functions(
        &self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), TypeError> {
        let mut func_ids = vec![];
        let mut placeholder_substitutions = HashMap::new();

        // Predeclaration pass, just declare placeholders
        for id in root_ids.iter() {
            let Expr::Func {
                name: Some(Name::Resolved(symbol_id, name_str)),
                ..
            } = source_file.get(id).unwrap().clone()
            else {
                continue;
            };

            let placeholder = env.placeholder(id, name_str.clone(), &symbol_id);

            // Stash this func ID so we can fully infer it in the next loop
            func_ids.push((id, symbol_id, placeholder.clone()));

            env.declare(
                symbol_id,
                Scheme {
                    ty: placeholder,
                    unbound_vars: vec![],
                },
            );
        }

        for (expr_id, symbol_id, placeholder) in func_ids {
            let Ty::TypeVar(type_var_id) = placeholder.clone() else {
                unreachable!()
            };

            let fn_var = self.infer_node(expr_id, env, &Some(placeholder), source_file)?;
            let scheme = env.generalize(&fn_var);
            env.declare(symbol_id, scheme);

            placeholder_substitutions.insert(type_var_id.clone(), fn_var);
        }

        env.replace_constraint_values(placeholder_substitutions);

        Ok(())
    }
}
