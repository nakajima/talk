use std::{collections::HashMap, fmt::Display, hash::Hash};

use crate::{
    NameResolved, SymbolID, SymbolTable, Typed,
    diagnostic::Diagnostic,
    environment::{EnumVariant, Method, Property, StructDef, free_type_vars},
    expr::{Expr, Pattern},
    match_builtin,
    name::Name,
    name_resolver::NameResolverError,
    parser::ExprID,
    source_file::SourceFile,
    synthesis::synthesize_inits,
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

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    Void,
    Int,
    Bool,
    Float,
    Init(SymbolID, FuncParams),
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
    Pointer,
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Void => write!(f, "void"),
            Ty::Int => write!(f, "Int"),
            Ty::Bool => write!(f, "Bool"),
            Ty::Float => write!(f, "Float"),
            Ty::Init(_, params) => write!(
                f,
                "init({})",
                params
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty::Func(params, ty, _) => write!(
                f,
                "func({}) -> {ty}",
                params
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty::Closure { func, .. } => write!(f, "{func}"),
            Ty::TypeVar(type_var_id) => write!(f, "{type_var_id:?}"),
            Ty::Enum(_, _) => write!(f, "enum"),
            Ty::EnumVariant(_, _) => write!(f, "enum variant"),
            Ty::Tuple(items) => write!(
                f,
                "({})",
                items
                    .iter()
                    .map(|i| format!("{i}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty::Array(ty) => write!(f, "Array<{ty}>"),
            Ty::Struct(_, _) => write!(f, "struct"),
            Ty::Pointer => write!(f, "pointer"),
        }
    }
}

impl Hash for Ty {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        format!("{self:?}").hash(state);
    }
}

impl Eq for Ty {}

impl Ty {
    pub fn optional(&self) -> Ty {
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
        self.infer_without_prelude(env, source_file, symbol_table)
    }

    pub fn hoist(
        &self,
        items: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
        symbol_table: &mut SymbolTable,
    ) {
        if let Err((id, err)) = self.hoist_structs(items, env, source_file, symbol_table) {
            source_file.diagnostics.insert(Diagnostic::typing(id, err));
        }

        if let Err((id, err)) = self.hoist_enums(items, env, source_file, symbol_table) {
            source_file.diagnostics.insert(Diagnostic::typing(id, err));
        }

        self.hoist_functions(items, env, source_file);
    }

    pub fn infer_without_prelude(
        &self,
        env: &mut Environment,
        mut source_file: SourceFile<NameResolved>,
        symbol_table: &mut SymbolTable,
    ) -> SourceFile<Typed> {
        let root_ids = source_file.root_ids();
        synthesize_inits(&mut source_file, symbol_table, env);
        self.hoist(&root_ids, env, &mut source_file, symbol_table);

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
                self.infer_let(env, *symbol_id, rhs, expected, source_file)
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
            Expr::Block(_) => self.infer_block(id, env, expected, source_file),
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
            Expr::Variable(Name::Raw(name_str), _) => Err(TypeError::Unresolved(name_str.clone())),
            Expr::Variable(Name::_Self(sym), _) => env.instantiate_symbol(*sym),
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
                Some(Expr::Property { .. }) => continue, // Properties are handled by the hoisting
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
        _id: &ExprID,
        env: &mut Environment,
        callee: &ExprID,
        type_args: &[ExprID],
        args: &[ExprID],
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        log::info!("infer call");
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
            Some(Expr::Variable(Name::Resolved(symbol_id, _), _))
                if env.is_struct_symbol(&symbol_id) =>
            {
                let struct_def = env.lookup_struct(&symbol_id).unwrap();

                // TODO: Handle multiple initializers
                // TODO: Handle multiple initializers
                log::info!("looking up initializer for struct: {struct_def:?}");
                let Some(Expr::Init(_, func_id)) =
                    source_file.get(&struct_def.initializers[0].1).cloned()
                else {
                    return Err(TypeError::Unknown(
                        "Unable to determine initializer for struct".into(),
                    ));
                };

                // Instantiate the struct type to get fresh type variables for its generics
                let instantiated = env.instantiate_symbol(symbol_id)?;

                // Infer the init function type
                let init_func_ty = self.infer_node(&func_id, env, expected, source_file)?;

                let Ty::Func(params, _, _) = init_func_ty else {
                    return Err(TypeError::Unknown("Could not get init func".into()));
                };

                // Create the Init type with the instantiated struct's symbol and the function's params
                let init_ty = Ty::Init(symbol_id, params.clone());

                // Insert the typed expression for the callee (the struct name being called)
                env.typed_exprs.insert(
                    *callee,
                    TypedExpr {
                        id: *callee,
                        expr: source_file.get(callee).cloned().unwrap(),
                        ty: init_ty.clone(),
                    },
                );

                // Constrain the Init type parameters to match the provided arguments
                env.constrain_equality(*callee, Ty::Init(symbol_id, arg_tys), init_ty);

                // The return type is the instantiated struct type
                ret_var = instantiated;
            }
            _ => {
                let callee_ty = self.infer_node(callee, env, &None, source_file)?;
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
                    env.instantiate_symbol(*symbol_id)?
                }
            }
            Name::_Self(symbol_id) => env.instantiate_symbol(*symbol_id)?,
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
            log::debug!("Declared scheme for named func {symbol_id:?} {scheme:?}");
            env.declare(*symbol_id, scheme);
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
        for param in params.iter() {
            let expr = source_file.get(param).cloned();
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
                    *param,
                    TypedExpr {
                        id: *param,
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
                .filter_map(|c| c.ok())
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
        ty
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
        self.hoist_functions(&items, env, source_file);

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
        symbol_table: &mut SymbolTable,
    ) -> Result<(), (ExprID, TypeError)> {
        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();
            let Expr::Struct(name, generics, body) = expr else {
                continue;
            };

            let Name::Resolved(symbol_id, name_str) = name else {
                return Err((*id, TypeError::Unresolved(name.name_str())));
            };

            let Some(Expr::Block(expr_ids)) = source_file.get(&body).cloned() else {
                unreachable!()
            };

            let mut methods: HashMap<String, Method> = Default::default();
            let mut properties: Vec<Property> = Default::default();
            let mut type_parameters = vec![];
            let default_initializers = vec![];
            let initializers = symbol_table
                .initializers_for(&symbol_id)
                .unwrap_or(&default_initializers);

            for id in generics {
                match self.infer_node(&id, env, &None, source_file) {
                    Ok(ty) => type_parameters.push(ty),
                    Err(e) => {
                        source_file.diagnostics.insert(Diagnostic::typing(id, e));
                    }
                }
            }

            // Manually create the scheme with the type parameters as unbound variables
            let unbound_vars: Vec<TypeVarID> = type_parameters
                .iter()
                .filter_map(|ty| {
                    if let Ty::TypeVar(var) = ty {
                        Some(var.clone())
                    } else {
                        None
                    }
                })
                .collect();

            let scheme = Scheme::new(
                Ty::Struct(symbol_id, type_parameters.clone()),
                unbound_vars.clone(),
            );
            env.declare(symbol_id, scheme.clone());

            // Define a placeholder for `self` references
            env.register_struct(StructDef::new(
                symbol_id,
                name_str.clone(),
                type_parameters.clone(),
                properties.clone(),
                methods.clone(),
                initializers
                    .iter()
                    .map(|i| (source_file.path.clone(), *i))
                    .collect(),
            ));

            for expr_id in expr_ids {
                match &source_file.get(&expr_id).cloned().unwrap() {
                    Expr::Property {
                        name,
                        type_repr,
                        default_value,
                    } => {
                        let mut ty = None;
                        if let Some(type_repr) = type_repr {
                            ty = Some(
                                self.infer_node(type_repr, env, &None, source_file)
                                    .map_err(|e| (expr_id, e))?,
                            )
                        }
                        if let Some(default_value) = default_value {
                            ty = Some(
                                self.infer_node(default_value, env, &None, source_file)
                                    .map_err(|e| (expr_id, e))?,
                            );
                        }
                        if ty.is_none() {
                            return Err((expr_id, TypeError::Unknown("No type for method".into())));
                        }

                        let (symbol, name) = match name.clone() {
                            Name::Resolved(symbol, name_str) => (symbol, name_str),
                            _ => unreachable!(),
                        };

                        log::trace!("Defining property {name:?} {ty:?}");
                        properties.push(Property::new(name.to_string(), ty.unwrap(), symbol));
                    }
                    Expr::Init(_, func_id) => {
                        self.infer_node(func_id, env, &None, source_file).ok();
                    }
                    Expr::Func { name, .. } => {
                        let name = match name.clone() {
                            Some(Name::Raw(name_str)) => name_str,
                            Some(Name::Resolved(_, name_str)) => name_str,
                            _ => unreachable!(),
                        };

                        let ty = self
                            .infer_node(&expr_id, env, &None, source_file)
                            .map_err(|e| (expr_id, e))?;
                        log::trace!("Defining property {name:?} {ty:?}");
                        methods.insert(name.to_string(), Method::new(name.to_string(), ty));
                    }
                    _ => {
                        return {
                            log::error!("Unhandled property: {:?}", source_file.get(&expr_id));
                            Err((
                                *id,
                                TypeError::Unknown(format!(
                                    "Unhandled property: {:?}",
                                    source_file.get(&expr_id)
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

    fn hoist_enums(
        &self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
        symbol_table: &mut SymbolTable,
    ) -> Result<(), (ExprID, TypeError)> {
        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();

            if let Expr::EnumDecl(Name::Resolved(enum_id, _), generics, body) = expr.clone() {
                let Some(Expr::Block(expr_ids)) = source_file.get(&body).cloned() else {
                    unreachable!()
                };

                env.start_scope();
                let mut generic_vars = vec![];
                for generic_id in generics {
                    let ty = self
                        .infer_node(&generic_id, env, &None, source_file)
                        .map_err(|e| (generic_id, e))?;
                    generic_vars.push(ty);
                }

                let enum_ty = Ty::Enum(enum_id, generic_vars.clone());
                let scheme = env.generalize(&enum_ty);
                log::trace!("enum scheme: {scheme:?}");
                env.declare_in_parent(enum_id, scheme);

                let mut methods: HashMap<String, Method> = Default::default();
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

                    if let Expr::Func { name, .. } = &expr {
                        let ty = self
                            .infer_node(&expr_id, env, &None, source_file)
                            .map_err(|e| (expr_id, e))?;
                        let name_str = name.clone().unwrap().name_str();
                        methods.insert(name_str.clone(), Method::new(name_str, ty));
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
                            symbol_table
                                .get(&enum_id)
                                .map(|s| s.definition.clone())
                                .unwrap(),
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
            } else {
                log::warn!("not a func {expr:?}");
            }
        }
    }
}
