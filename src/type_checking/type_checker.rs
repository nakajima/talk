use std::{collections::HashMap, hash::Hash};

use crate::{
    NameResolved, SymbolID, SymbolTable, Typed,
    constraint_solver::{Constraint, Substitutions},
    diagnostic::Diagnostic,
    environment::{EnumVariant, Method, RawEnumVariant, RawMethod},
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

#[derive(Clone)]
pub struct TypeVarID(pub i32, pub TypeVarKind);

impl PartialEq for TypeVarID {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for TypeVarID {}

impl Hash for TypeVarID {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_i32(self.0);
    }
}

impl TypeVarID {
    pub fn canonicalized(&self) -> Option<TypeVarID> {
        if let TypeVarKind::Instantiated(parent_id) = self.1 {
            return Some(TypeVarID(parent_id, TypeVarKind::Unbound));
        }

        None
    }
}

impl std::fmt::Debug for TypeVarID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.1 {
            TypeVarKind::Blank => write!(f, "T{}[blank]", self.0),
            TypeVarKind::CallArg => write!(f, "T{}[arg]", self.0),
            TypeVarKind::CallReturn => write!(f, "T{}[ret]", self.0),
            TypeVarKind::FuncParam(name) => write!(f, "T{}[param({})]", self.0, name),
            TypeVarKind::FuncType => write!(f, "T{}[func]", self.0),
            TypeVarKind::FuncNameVar(symbol_id) => write!(f, "T{}[${}]", self.0, symbol_id.0),
            TypeVarKind::FuncBody => write!(f, "T{}[body]", self.0),
            TypeVarKind::Let => write!(f, "T{}[let]", self.0),
            TypeVarKind::TypeRepr(name) => write!(f, "T{}[<{:?}>]", self.0, name),
            TypeVarKind::Member(name) => write!(f, "T{}[.{}]", self.0, name),
            TypeVarKind::Element => write!(f, "T{}[E]", self.0),
            TypeVarKind::VariantValue => write!(f, "T{}[variant]", self.0),
            TypeVarKind::PatternBind(name) => write!(f, "T{}[->{}]", self.0, name.name_str()),
            TypeVarKind::CanonicalTypeParameter(name) => {
                write!(f, "T{}[C<{}>]", self.0, name)
            }
            TypeVarKind::Placeholder(name) => write!(f, "T{}[...{}]", self.0, name),
            TypeVarKind::Instantiated(from) => write!(f, "T{}[Inst.({})]", self.0, from),
            TypeVarKind::Unbound => write!(f, "T{}[?]", self.0),
        }
    }
}

#[derive(Clone, PartialEq, Debug, Eq, Hash)]
pub enum TypeVarKind {
    Blank,
    CallArg,
    CallReturn,
    FuncParam(String),
    FuncType,
    FuncNameVar(SymbolID),
    FuncBody,
    Let,
    TypeRepr(Name),
    Member(String),
    Element,
    VariantValue,
    PatternBind(Name),
    CanonicalTypeParameter(String),
    Placeholder(String),
    Instantiated(i32),
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
    ArgumentError(String),
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
            Self::ArgumentError(message) => message.to_string(),
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
pub struct TypeChecker<'a> {
    pub(crate) symbol_table: &'a mut SymbolTable,
}

#[allow(unused)]
macro_rules! indented_println {
    // Matcher:
    // - $env: An expression that evaluates to your environment struct.
    // - $fmt: The literal format string.
    // - $($args:expr)*: A repeating sequence of zero or more comma-separated expressions
    //   for the arguments.
    ($env:expr, $fmt:literal $(, $args:expr)*) => {
        // Expander:
        // This is the code that will be generated.
        println!(
            // `concat!` joins the initial indent placeholder "{}" with your format string.
            // e.g., concat!("{}", "Infer node {}: {:?}") -> "{}Infer node {}: {:?}"
            concat!("{}", $fmt),

            // The first argument is always the calculated whitespace string.
            (0..$env.scopes.len()).map(|_| "  ").collect::<String>(),

            // The subsequent, user-provided arguments are passed along.
            $($args),*
        );
    };
}

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

impl<'a> TypeChecker<'a> {
    pub fn new(symbol_table: &'a mut SymbolTable) -> Self {
        Self { symbol_table }
    }

    pub fn infer(
        &mut self,
        source_file: SourceFile<NameResolved>,
        env: &mut Environment,
    ) -> SourceFile<Typed> {
        self.infer_without_prelude(env, source_file)
    }

    pub fn predeclare(
        &mut self,
        items: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), TypeError> {
        // Predeclare lets
        self.predeclare_lets(items, env, source_file);

        if let Err((id, err)) = self.predeclare_structs(items, env, source_file) {
            source_file.diagnostics.insert(Diagnostic::typing(id, err));
        }

        if let Err((id, err)) = self.predeclare_enums(items, env, source_file) {
            source_file.diagnostics.insert(Diagnostic::typing(id, err));
        }

        self.predeclare_functions(items, env, source_file)?;

        Ok(())
    }

    pub fn infer_without_prelude(
        &mut self,
        env: &mut Environment,
        mut source_file: SourceFile<NameResolved>,
    ) -> SourceFile<Typed> {
        let root_ids = source_file.root_ids();
        synthesize_inits(&mut source_file, self.symbol_table, env);

        // Just define names for all of the funcs, structs and enums
        self.predeclare(&root_ids, env, &mut source_file).ok();

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

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn infer_node(
        &self,
        id: &ExprID,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        if let Some(typed_expr) = env.typed_exprs.get(id) {
            log::trace!("Already inferred {:?}, returning from cache", typed_expr);
            return Ok(typed_expr.ty.clone());
        }

        let expr = source_file.get(id).unwrap().clone();
        // indented_println!(
        //     env,
        //     "Infer node {}: {:?} {}:{}",
        //     id,
        //     expr,
        //     std::panic::Location::caller().file(),
        //     std::panic::Location::caller().line()
        // );
        log::trace!("Infer node: {:?}", expr);
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
            Expr::Parameter(name @ Name::Resolved(_, _), param_ty) => {
                self.infer_parameter(name, param_ty, env, source_file)
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
            Expr::EnumVariant(name, values) => {
                self.infer_enum_variant(name, values, expected, env, source_file)
            }
            Expr::Match(pattern, items) => self.infer_match(env, pattern, items, source_file),
            Expr::MatchArm(pattern, body) => {
                self.infer_match_arm(env, pattern, body, expected, source_file)
            }
            Expr::PatternVariant(_, _, _items) => self.infer_pattern_variant(id, env),
            Expr::Member(receiver, member_name) => {
                self.infer_member(id, env, receiver, member_name, source_file)
            }
            Expr::Pattern(pattern) => {
                self.infer_pattern_expr(id, env, pattern, expected, source_file)
            }
            Expr::Variable(Name::Raw(name_str), _) => Err(TypeError::Unresolved(name_str.clone())),
            Expr::Variable(Name::_Self(sym), _) => self.infer_variable(id, env, *sym, "self"),
            Expr::Return(rhs) => self.infer_return(rhs, env, expected, source_file),
            Expr::LiteralArray(items) => self.infer_array(items, env, expected, source_file),
            Expr::Struct(name, generics, body) => {
                self.infer_struct(name, generics, body, env, expected, source_file)
            }
            Expr::CallArg { value, .. } => self.infer_node(value, env, expected, source_file),
            Expr::Init(Some(struct_id), func_id) => {
                self.infer_init(struct_id, func_id, expected, env, source_file)
            }
            Expr::Property {
                name,
                type_repr,
                default_value,
            } => self.infer_property(&id, name, type_repr, default_value, env, source_file),
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

    fn infer_property(
        &self,
        expr_id: &ExprID,
        name: &Name,
        type_repr: &Option<ExprID>,
        default_value: &Option<ExprID>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let type_repr = type_repr
            .map(|id| self.infer_node(&id, env, &None, source_file))
            .transpose()?;
        let default_value = default_value
            .map(|id| self.infer_node(&id, env, &None, source_file))
            .transpose()?;

        let ty = match (type_repr, default_value) {
            (Some(type_repr), Some(default_value)) => {
                env.constrain_equality(*expr_id, type_repr.clone(), default_value);
                type_repr
            }
            (None, Some(default_value)) => default_value,
            (Some(type_repr), None) => type_repr,
            (None, None) => env.placeholder(expr_id, name.name_str(), &name.try_symbol_id()),
        };

        Ok(ty)
    }

    fn infer_enum_decl(
        &self,
        enum_id: &SymbolID,
        _body: &ExprID,
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
            inferred_methods.insert(
                name.clone(),
                Method::new(name.clone(), raw_method.expr_id, method_ty),
            );
        }

        let mut inferred_variants = vec![];
        for variant in enum_def.raw_variants {
            let ty = self
                .infer_node(&variant.expr_id, env, &None, source_file)?
                .clone();
            inferred_variants.push(EnumVariant {
                name: variant.name,
                ty,
            });
        }

        let enum_def_mut = env.lookup_enum_mut(enum_id).unwrap();
        enum_def_mut.methods = inferred_methods;
        enum_def_mut.variants = inferred_variants;

        let scheme = env.lookup_symbol(enum_id)?;
        Ok(scheme.ty.clone())
    }

    fn infer_enum_variant(
        &self,
        _name: &Name,
        values: &[ExprID],
        expected: &Option<Ty>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let Some(Ty::Enum(enum_id, _)) = expected else {
            unreachable!("should always be called with expected = Enum");
        };
        let values = self.infer_nodes(values, env, source_file)?;
        Ok(Ty::EnumVariant(*enum_id, values))
    }

    fn infer_parameter(
        &self,
        name: &Name,
        param_ty: &Option<ExprID>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let param_ty = if let Some(param_ty) = &param_ty {
            self.infer_node(param_ty, env, &None, source_file)?
        } else {
            Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncParam(name.name_str())))
        };

        // Parameters are monomorphic inside the function body
        let scheme = Scheme::new(param_ty.clone(), vec![]);
        env.declare(name.try_symbol_id(), scheme);

        Ok(param_ty)
    }

    fn infer_init(
        &self,
        struct_id: &SymbolID,
        func_id: &ExprID,
        expected: &Option<Ty>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let inferred = self.infer_node(func_id, env, expected, source_file)?;
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

        Ok(Ty::Init(*struct_id, params, vec![]))
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

        let Some(Expr::Block(body_ids)) = source_file.get(body).cloned() else {
            unreachable!()
        };

        for id in body_ids {
            match source_file.get(&id) {
                // Some(Expr::Property {
                //     name,
                //     type_repr,
                //     default_value,
                // }) => {
                //     println!("hi");
                // }
                _ => {
                    self.infer_node(&id, env, expected, source_file)?;
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
        _id: &ExprID,
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
            Some(Expr::Variable(Name::Resolved(symbol_id, _), _))
                if env.is_struct_symbol(&symbol_id) =>
            {
                let placeholder =
                    env.placeholder(callee, format!("init({:?})", symbol_id), &symbol_id);

                env.typed_exprs.insert(
                    *callee,
                    TypedExpr {
                        id: *callee,
                        expr: source_file.get(callee).cloned().unwrap(),
                        ty: placeholder.clone(),
                    },
                );

                env.constraints.push(Constraint::InitializerCall {
                    expr_id: *callee,
                    initializes_id: symbol_id,
                    args: arg_tys.clone(),
                    ret: placeholder.clone(),
                });

                ret_var = Ty::Struct(symbol_id, vec![]);
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
        id: &ExprID,
        env: &mut Environment,
        name: &Name,
        generics: &[ExprID],
        is_type_parameter: &bool,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let symbol_id = name.try_symbol_id();

        if *is_type_parameter {
            let scheme = env.lookup_symbol(&symbol_id).cloned().unwrap_or(Scheme {
                ty: env.placeholder(id, name.name_str(), &symbol_id),
                unbound_vars: vec![],
            });

            env.declare(symbol_id, scheme.clone());

            return Ok(scheme.ty.clone());
        }

        let base_ty_placeholder = env.ty_for_symbol(id, name.name_str(), &symbol_id);

        // If there are no generic arguments (`let x: Int`), we are done.
        if generics.is_empty() {
            return Ok(base_ty_placeholder);
        }

        let ty_scheme = env.lookup_symbol(&symbol_id).unwrap().clone();

        let mut substitutions = Substitutions::default();
        for (var, generic_id) in ty_scheme.unbound_vars.iter().zip(generics) {
            // Recursively get arg_ty
            let arg_ty = self.infer_node(generic_id, env, &None, source_file)?;
            substitutions.insert(var.clone(), arg_ty);
        }

        let instantiated = env.instantiate_with_args(&ty_scheme, substitutions.clone());

        // indented_println!(
        //     env,
        //     "type repr {:?} -> {:?} {:?}",
        //     name,
        //     instantiated,
        //     substitutions
        // );

        Ok(instantiated)
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

        // indented_println!(
        //     env,
        //     "&& infer_func_type_repr: ({:?}) -> {:?}",
        //     inferred_args,
        //     inferred_ret
        // );

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
        _id: &ExprID,
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

        if let Some(Name::Resolved(symbol_id, _)) = name
            && let Ok(scheme) = env.lookup_symbol(symbol_id).cloned()
        {
            env.declare(*symbol_id, scheme.clone());
            // Some(env.instantiate(&scheme))
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
        let mut ret_ty = body_ty.clone();

        if let Some(ret_type) = expected_body_ty
            && let Some(ret_id) = ret
        {
            ret_ty = ret_type.clone();
            env.constrain_equality(*ret_id, body_ty.clone(), ret_type.clone());
        }

        env.end_scope();

        let func_ty = Ty::Func(param_vars.clone(), Box::new(ret_ty), inferred_generics);
        let inferred_ty = if captures.is_empty() {
            func_ty
        } else {
            Ty::Closure {
                func: func_ty.into(),
                captures: captures.to_vec(),
            }
        };

        // if let Some(predeclared_ty) = predeclared_ty {
        //     env.constrain_equality(*id, predeclared_ty, inferred_ty.clone());
        // }

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
        _id: &ExprID,
        env: &mut Environment,
        symbol_id: SymbolID,
        _name: &str,
    ) -> Result<Ty, TypeError> {
        let scheme = env.lookup_symbol(&symbol_id)?.clone();
        let ty = env.instantiate(&scheme);
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
        self.predeclare_lets(&items, env, source_file);
        self.predeclare_functions(&items, env, source_file)?;

        let mut block_return_ty = expected.clone();
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

        log::warn!("infer_block: {block_return_ty:?}");

        Ok(block_return_ty.unwrap_or(Ty::Void))
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
                let member_var =
                    env.new_type_variable(TypeVarKind::Member(member_name.to_string()));

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

                let member_var = Ty::TypeVar(
                    env.new_type_variable(TypeVarKind::Member(member_name.to_string())),
                );

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
        id: &ExprID,
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

        self.infer_pattern(id, pattern, env, expected, source_file)?;
        Ok(expected.clone())
    }

    fn infer_pattern(
        &self,
        id: &ExprID,
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
                            expr_id: *id,
                            scrutinee_ty: expected.clone(),
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

    fn predeclare_enums(
        &self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), (ExprID, TypeError)> {
        let mut enum_defs = vec![];
        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();

            let Expr::EnumDecl(Name::Resolved(enum_id, enum_name_str), generics, body) =
                expr.clone()
            else {
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

                let ty = Ty::TypeVar(env.new_type_variable(TypeVarKind::CanonicalTypeParameter(
                    format!("{}{}", name_str, symbol_id.0),
                )));

                env.declare(
                    *symbol_id,
                    Scheme {
                        ty: ty.clone(),
                        unbound_vars: vec![],
                    },
                );
                generic_vars.push(ty);
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

                if let Expr::EnumVariant(name, values) = source_file.get(&expr_id).cloned().unwrap()
                {
                    variant_defs.push(RawEnumVariant {
                        name: name.name_str(),
                        expr_id: expr_id,
                        values,
                    });
                } else {
                    log::debug!("Non-raw expr: {:?}", source_file.get(&expr_id).unwrap());
                }
            }

            let enum_def = EnumDef {
                name: Some(enum_id),
                name_str: enum_name_str,
                raw_variants: variant_defs,
                variants: Default::default(),
                type_parameters: generic_vars,
                raw_methods,
                methods: Default::default(),
            };

            enum_defs.push(enum_def.clone());
            env.register_enum(enum_def);
        }

        for enum_def in &mut enum_defs {
            let mut methods = HashMap::new();
            let mut variants = vec![];

            for (_, raw_method) in enum_def.raw_methods.iter() {
                let ty = self
                    .infer_node(&raw_method.expr_id, env, &None, source_file)
                    .map_err(|e| (raw_method.expr_id, e))?;
                methods.insert(
                    raw_method.name.clone(),
                    Method::new(raw_method.name.clone(), raw_method.expr_id, ty),
                );
            }

            for raw_variant in enum_def.raw_variants.iter() {
                let ty = self
                    .infer_node(
                        &raw_variant.expr_id,
                        env,
                        &Some(Ty::Enum(
                            enum_def.name.unwrap(),
                            enum_def.type_parameters.clone(),
                        )),
                        source_file,
                    )
                    .map_err(|e| (raw_variant.expr_id, e))?;
                variants.push(EnumVariant {
                    name: raw_variant.name.clone(),
                    ty: ty,
                });
            }

            enum_def.methods = methods;
            enum_def.variants = variants;
            env.register_enum(enum_def.clone());
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

            let placeholder = env.placeholder(id, format!("predecl[{}]", name_str), &symbol_id);

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

        env.replace_typed_exprs_values(&placeholder_substitutions);
        env.replace_constraint_values(&placeholder_substitutions);

        Ok(())
    }

    fn predeclare_lets(
        &self,
        items: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) {
        for id in items {
            let Some(Expr::Assignment(lhs, _)) = source_file.get(&id).cloned() else {
                continue;
            };

            let Some(Expr::Let(Name::Resolved(_, _), _)) = source_file.get(&lhs) else {
                continue;
            };

            self.infer_node(&id, env, &None, source_file).ok();
        }
    }
}
