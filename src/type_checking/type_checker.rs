use std::{collections::HashMap, hash::Hash};

use crate::{
    NameResolved, SymbolID, SymbolTable, Typed,
    compiling::compilation_session::SharedCompilationSession,
    conformance_checker::ConformanceError,
    constraint_solver::{Constraint, ConstraintSolver, Substitutions},
    diagnostic::Diagnostic,
    expr::{Expr, IncompleteExpr, Pattern},
    name::Name,
    name_resolver::NameResolverError,
    parser::ExprID,
    source_file::SourceFile,
    synthesis::synthesize_inits,
    token_kind::TokenKind,
    ty::Ty,
    type_constraint::TypeConstraint,
    type_defs::TypeDef,
    type_var_id::{TypeVarID, TypeVarKind},
};

use super::{environment::Environment, typed_expr::TypedExpr};

pub type TypeDefs = HashMap<SymbolID, TypeDef>;
pub type FuncParams = Vec<Ty>;
pub type FuncReturning = Box<Ty>;

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum TypeError {
    Unresolved(String),
    NameResolution(NameResolverError),
    UnknownEnum(Name),
    UnknownVariant(Name),
    Unknown(String),
    UnexpectedType(String, String),
    Mismatch(String, String),
    ArgumentError(String),
    Handled, // If we've already reported it
    OccursConflict,
    ConformanceError(Vec<ConformanceError>),
    Nonconformance(String, String),
    MemberNotFound(String, String),
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
            Self::Nonconformance(protocol, structname) => {
                format!("{structname} does not conform to the {protocol} protocol")
            }
            Self::MemberNotFound(name, receiver) => {
                format!("Cannot find member named {name} for {receiver}")
            }
            Self::ConformanceError(err) => {
                format!("{err:?}")
            }
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
    session: SharedCompilationSession,
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
                    return Err(TypeError::UnexpectedType(
                        expected.to_string(),
                        actual.to_string(),
                    ));
                }
            }
        }
    }

    Ok(actual)
}

impl<'a> TypeChecker<'a> {
    pub fn new(session: SharedCompilationSession, symbol_table: &'a mut SymbolTable) -> Self {
        Self {
            session,
            symbol_table,
        }
    }

    pub fn infer(
        &mut self,
        source_file: SourceFile<NameResolved>,
        env: &mut Environment,
    ) -> SourceFile<Typed> {
        self.infer_without_prelude(env, source_file)
    }

    pub fn infer_without_prelude(
        &mut self,
        env: &mut Environment,
        mut source_file: SourceFile<NameResolved>,
    ) -> SourceFile<Typed> {
        let root_ids = source_file.root_ids();
        synthesize_inits(&mut source_file, self.symbol_table, env);

        // Just define names for all of the funcs, structs and enums
        if let Err(e) = self.hoist(&root_ids, env, &mut source_file)
            && let Ok(mut lock) = self.session.lock()
        {
            lock.add_diagnostic(Diagnostic::typing(
                source_file.path.clone(),
                *root_ids.first().unwrap_or(&0),
                e,
            ));
        }

        let mut typed_roots = vec![];
        for id in &root_ids {
            #[allow(clippy::unwrap_used)]
            match self.infer_node(id, env, &None, &mut source_file) {
                Ok(_ty) => typed_roots.push(env.typed_exprs.get(id).unwrap().clone()),
                Err(e) => {
                    if let Ok(mut lock) = self.session.lock() {
                        lock.add_diagnostic(Diagnostic::typing(source_file.path.clone(), *id, e))
                    }
                }
            }
        }

        source_file.to_typed()
    }

    pub fn infer_nodes(
        &mut self,
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
        &mut self,
        id: &ExprID,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        if let Some(typed_expr) = env.typed_exprs.get(id)
            && expected.is_none()
        {
            log::trace!("Already inferred {typed_expr:?}, returning from cache");
            return Ok(typed_expr.ty.clone());
        }

        let Some(expr) = source_file.get(id).cloned() else {
            return Err(TypeError::Unknown(format!("No expr found with id {id}")));
        };

        log::trace!("Infer node [{id}]: {expr:?}");
        let mut ty = match &expr {
            Expr::Incomplete(expr_id) => {
                self.handle_incomplete(expr_id, expected, env, source_file)
            }
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
            Expr::LiteralString(_) => Ok(Ty::string()),
            Expr::Assignment(lhs, rhs) => self.infer_assignment(env, lhs, rhs, source_file),
            Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => self.infer_type_repr(
                id,
                env,
                name,
                generics,
                conformances,
                introduces_type,
                source_file,
            ),
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
                env,
                name,
                generics,
                params,
                captures,
                body,
                ret,
                source_file,
            ),
            Expr::Let(Name::Resolved(symbol_id, _), rhs) => {
                self.infer_let(env, *symbol_id, rhs, expected, source_file)
            }
            Expr::Variable(name, _) => self.infer_variable(env, name),
            Expr::Parameter(name @ Name::Resolved(_, _), param_ty) => {
                self.infer_parameter(name, param_ty, env, source_file)
            }
            Expr::Tuple(types) => self.infer_tuple(types, env, source_file),
            Expr::Unary(_token_kind, rhs) => self.infer_unary(rhs, expected, env, source_file),
            Expr::Binary(lhs, op, rhs) => {
                self.infer_binary(id, lhs, rhs, op, expected, env, source_file)
            }
            Expr::Block(_) => self.infer_block(id, env, expected, source_file),
            Expr::EnumDecl {
                name: Name::Resolved(symbol_id, _),
                body,
                ..
            } => self.infer_enum_decl(symbol_id, body, env, source_file),
            Expr::EnumVariant(name, values) => {
                self.infer_enum_variant(name, values, expected, env, source_file)
            }
            Expr::Match(pattern, items) => self.infer_match(env, pattern, items, source_file),
            Expr::MatchArm(pattern, body) => {
                self.infer_match_arm(env, pattern, body, expected, source_file)
            }
            Expr::PatternVariant(_, _, _items) => self.infer_pattern_variant(id, env),
            Expr::Member(receiver, member_name) => {
                self.infer_member(id, env, receiver, member_name, expected, source_file)
            }
            Expr::Pattern(pattern) => {
                self.infer_pattern_expr(id, env, pattern, expected, source_file)
            }
            Expr::Return(rhs) => self.infer_return(rhs, env, expected, source_file),
            Expr::LiteralArray(items) => self.infer_array(items, env, expected, source_file),
            Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => self.infer_struct(
                name,
                generics,
                conformances,
                body,
                env,
                expected,
                source_file,
            ),
            Expr::Extend {
                name,
                generics,
                conformances,
                body,
            } => self.infer_extension(
                name,
                generics,
                conformances,
                body,
                env,
                expected,
                source_file,
            ),
            Expr::CallArg { value, .. } => self.infer_node(value, env, expected, source_file),
            Expr::Init(Some(struct_id), func_id) => {
                self.infer_init(struct_id, func_id, expected, env, source_file)
            }
            Expr::Property {
                name,
                type_repr,
                default_value,
            } => self.infer_property(id, name, type_repr, default_value, env, source_file),
            Expr::Break => Ok(Ty::Void),
            Expr::ProtocolDecl {
                name,
                associated_types,
                conformances,
                ..
            } => self.infer_protocol(name, associated_types, conformances, env, source_file),
            Expr::FuncSignature {
                params,
                generics,
                ret,
                ..
            } => {
                let params = self.infer_nodes(params, env, source_file)?;
                let generics = self.infer_nodes(generics, env, source_file)?;
                let ret = self.infer_node(ret, env, &None, source_file)?;
                Ok(Ty::Func(params, ret.into(), generics))
            }
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
                log::error!("error inferring {:?}: {:?}", source_file.get(id), e);
                if let Ok(mut lock) = self.session.lock() {
                    lock.add_diagnostic(Diagnostic::typing(
                        source_file.path.clone(),
                        *id,
                        e.clone(),
                    ));
                }
                ty = Err(TypeError::Handled);
            }
        }

        ty
    }

    fn handle_incomplete(
        &mut self,
        expr: &IncompleteExpr,
        expected: &Option<Ty>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        match expr {
            IncompleteExpr::Member(Some(receiver)) => {
                self.infer_node(receiver, env, expected, source_file)?;
                Ok(Ty::Void)
            }
            _ => Ok(Ty::Void),
        }
    }

    fn infer_protocol(
        &mut self,
        name: &Name,
        associated_types: &[ExprID],
        conformances: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let mut inferred_associated_types: Vec<Ty> = vec![];
        for generic in associated_types {
            inferred_associated_types
                .push(self.infer_node(generic, env, &None, source_file)?.clone());
        }

        for id in conformances {
            self.infer_node(id, env, &None, source_file)?;
        }

        let Name::Resolved(symbol_id, _) = name else {
            return Err(TypeError::Unresolved(name.name_str()));
        };

        Ok(Ty::Protocol(*symbol_id, inferred_associated_types))
    }

    fn infer_property(
        &mut self,
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
            (None, None) => env.placeholder(expr_id, name.name_str(), &name.symbol_id()?, vec![]),
        };

        Ok(ty)
    }

    fn infer_enum_decl(
        &self,
        enum_id: &SymbolID,
        _body: &ExprID,
        env: &mut Environment,
        _source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let scheme = env.lookup_symbol(enum_id)?;
        Ok(scheme.ty.clone())
    }

    fn infer_enum_variant(
        &mut self,
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
        &mut self,
        name: &Name,
        param_ty: &Option<ExprID>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let param_ty = if let Some(param_ty) = &param_ty {
            self.infer_node(param_ty, env, &None, source_file)?
        } else {
            Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncParam(name.name_str()), vec![]))
        };

        // Parameters are monomorphic inside the function body
        let scheme = Scheme::new(param_ty.clone(), vec![]);
        env.declare(name.symbol_id()?, scheme)?;

        Ok(param_ty)
    }

    fn infer_init(
        &mut self,
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

        Ok(Ty::Init(*struct_id, params))
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_extension(
        &mut self,
        name: &Name,
        generics: &[ExprID],
        conformances: &[ExprID],
        _body: &ExprID,
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

        for id in conformances {
            self.infer_node(id, env, expected, source_file)?;
        }

        let Name::Resolved(symbol_id, _) = name else {
            return Err(TypeError::Unresolved(name.name_str()));
        };

        Ok(Ty::Struct(*symbol_id, inferred_generics))
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_struct(
        &mut self,
        name: &Name,
        generics: &[ExprID],
        conformances: &[ExprID],
        _body: &ExprID,
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

        for id in conformances {
            self.infer_node(id, env, expected, source_file)?;
        }

        let Name::Resolved(symbol_id, _) = name else {
            return Err(TypeError::Unresolved(name.name_str()));
        };

        Ok(Ty::Struct(*symbol_id, inferred_generics))
    }

    fn infer_array(
        &mut self,
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
            .unwrap_or_else(|| Ty::TypeVar(env.new_type_variable(TypeVarKind::Element, vec![])));

        Ok(Ty::Struct(SymbolID::ARRAY, vec![ty]))
    }

    fn infer_return(
        &mut self,
        rhs: &Option<ExprID>,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        if let Some(rhs_id) = rhs {
            self.infer_node(rhs_id, env, expected, source_file)
        } else {
            Ok(Ty::Void)
        }
    }

    fn infer_loop(
        &mut self,
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
        &mut self,
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

    #[allow(clippy::too_many_arguments)]
    fn infer_call(
        &mut self,
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
            let call_return_var = env.new_type_variable(TypeVarKind::CallReturn, vec![]);
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

        let callee_expr = source_file.get(callee);
        match &callee_expr {
            // Handle struct initialization
            Some(Expr::Variable(Name::Resolved(symbol_id, _), _))
                if env.is_struct_symbol(symbol_id) =>
            {
                let Some(struct_def) = env.lookup_struct(symbol_id).cloned() else {
                    return Err(TypeError::Unknown(format!(
                        "Could not resolve symbol {symbol_id:?}"
                    )));
                };

                let placeholder =
                    env.placeholder(callee, format!("init({symbol_id:?})"), symbol_id, vec![]);

                env.typed_exprs.insert(
                    *callee,
                    TypedExpr {
                        id: *callee,
                        #[allow(clippy::expect_used)]
                        expr: callee_expr
                            .expect("we're already in the Some() arm")
                            .clone(),
                        ty: placeholder.clone(),
                    },
                );

                // If there aren't explicit type params specified, create some placeholders. I guess for now
                // if there are _some_ we'll just use positional values?
                let mut type_args = vec![];

                if !struct_def.type_parameters.is_empty() {
                    for (i, type_arg) in struct_def.type_parameters.iter().enumerate() {
                        type_args.push(if inferred_type_args.len().saturating_sub(1) > i {
                            inferred_type_args[i].clone()
                        } else {
                            env.placeholder(
                                id,
                                format!("Call Placeholder {type_arg:?}"),
                                &type_arg.id,
                                vec![],
                            )
                        });
                    }
                }

                ret_var = env.instantiate(&Scheme {
                    ty: Ty::Struct(*symbol_id, type_args),
                    unbound_vars: struct_def.canonical_type_vars(),
                });

                env.constraints.push(Constraint::InitializerCall {
                    expr_id: *callee,
                    initializes_id: *symbol_id,
                    args: arg_tys.clone(),
                    func_ty: placeholder.clone(),
                    result_ty: ret_var.clone(),
                });
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
        &mut self,
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

    #[allow(clippy::too_many_arguments)]
    fn infer_type_repr(
        &mut self,
        id: &ExprID,
        env: &mut Environment,
        name: &Name,
        generics: &[ExprID],
        conformances: &[ExprID],
        is_type_parameter: &bool,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let symbol_id = match name {
            Name::SelfType => match env.selfs.last() {
                Some(
                    Ty::Struct(symbol_id, _) | Ty::Enum(symbol_id, _) | Ty::Protocol(symbol_id, _),
                ) => *symbol_id,
                _ => {
                    return Err(TypeError::Unresolved(format!(
                        "Unable to get Self for {id}"
                    )));
                }
            },
            _ => name.symbol_id()?,
        };

        if *is_type_parameter {
            let mut unbound_vars = vec![];
            let mut type_constraints = vec![];

            for id in conformances {
                let ty = self.infer_node(id, env, &None, source_file)?;
                let Ty::Protocol(protocol_id, associated_types) = ty.clone() else {
                    return Err(TypeError::Unknown(format!("{ty:?} is not a protocol",)));
                };

                unbound_vars.extend(associated_types.iter().filter_map(|t| {
                    if let Ty::TypeVar(var) = t {
                        Some(var.clone())
                    } else {
                        None
                    }
                }));

                type_constraints.push(TypeConstraint::Conforms {
                    protocol_id,
                    associated_types: associated_types.clone(),
                });
            }

            let scheme = Scheme {
                ty: env.placeholder(id, name.name_str(), &symbol_id, type_constraints),
                unbound_vars,
            };

            env.declare(symbol_id, scheme.clone())?;

            return Ok(scheme.ty);
        }

        // If there are no generic arguments (`let x: Int`), we are done.
        if generics.is_empty() {
            let ty = if name == &Name::SelfType {
                env.placeholder(id, name.name_str(), &symbol_id, vec![])
            } else {
                env.ty_for_symbol(id, name.name_str(), &symbol_id, &[])
            };
            return Ok(ty);
        }

        let ty_scheme = env.lookup_symbol(&symbol_id)?.clone();
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
        &mut self,
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
        &mut self,
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
        &mut self,
        env: &mut Environment,
        name: &Option<Name>,
        generics: &[ExprID],
        params: &[ExprID],
        captures: &[SymbolID],
        body: &ExprID,
        ret: &Option<ExprID>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        env.start_scope();

        if let Some(Name::Resolved(symbol_id, _)) = name
            && let Ok(scheme) = env.lookup_symbol(symbol_id).cloned()
        {
            env.declare(*symbol_id, scheme.clone())?;
        };

        let mut inferred_generics = vec![];
        for generic in generics {
            if let Some(Expr::TypeRepr {
                name: Name::Resolved(symbol_id, _),
                ..
            }) = source_file.get(generic).cloned()
            {
                let ty = self.infer_node(generic, env, &None, source_file)?;
                inferred_generics.push(ty.clone());
                let scheme = Scheme::new(ty.clone(), vec![]);
                env.declare(symbol_id, scheme)?;
            } else {
                return Err(TypeError::Unresolved(
                    "could not resolve generic symbol".into(),
                ));
            }
        }

        let expected_ret_ty = if let Some(ret) = ret {
            Some(self.infer_node(ret, env, &None, source_file)?)
        } else {
            None
        };

        let mut param_vars: Vec<Ty> = vec![];
        for param in params.iter() {
            let param_ty = self.infer_node(param, env, &None, source_file)?;
            param_vars.push(param_ty);
        }

        let body_ty = self.infer_node(body, env, &expected_ret_ty, source_file)?;
        let mut ret_ty = body_ty.clone();

        if let Some(ret_type) = expected_ret_ty
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

        if let Some(Name::Resolved(symbol_id, _)) = name {
            // Declare a monomorphized scheme. It'll be generalized by the hoisting pass.
            env.declare(
                *symbol_id,
                Scheme {
                    ty: inferred_ty.clone(),
                    unbound_vars: vec![],
                },
            )?;
        }

        Ok(inferred_ty)
    }

    fn infer_let(
        &mut self,
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
            Ty::TypeVar(env.new_type_variable(TypeVarKind::Let, vec![]))
        };

        let scheme = Scheme::new(rhs_ty.clone(), vec![]);
        env.declare(symbol_id, scheme)?;

        Ok(rhs_ty)
    }

    fn infer_variable(&self, env: &mut Environment, name: &Name) -> Result<Ty, TypeError> {
        match name {
            Name::_Self(_sym) => {
                if let Some(self_) = env.selfs.last() {
                    Ok(self_.clone())
                } else {
                    Err(TypeError::Unknown("No value found for `self`".into()))
                }
            }
            Name::Resolved(symbol_id, _) => {
                let scheme = env.lookup_symbol(symbol_id)?.clone();
                let ty = env.instantiate(&scheme);
                Ok(ty)
            }
            Name::Raw(name_str) => Err(TypeError::Unresolved(name_str.clone())),
            Name::SelfType => env
                .selfs
                .last()
                .cloned()
                .ok_or(TypeError::Unknown("No type found for Self".to_string())),
        }
    }

    fn infer_tuple(
        &mut self,
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
        &mut self,
        rhs: &ExprID,
        expected: &Option<Ty>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        self.infer_node(rhs, env, expected, source_file)
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_binary(
        &mut self,
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
        &mut self,
        id: &ExprID,
        env: &mut Environment,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        let Some(Expr::Block(items)) = source_file.get(id).cloned() else {
            return Err(TypeError::Unknown("Didn't get block".into()));
        };

        env.start_scope();
        // self.hoist(&items, env, source_file)?;

        let mut block_return_ty = expected.clone();
        let mut ret_tys = vec![];

        for (i, item_id) in items.iter().enumerate() {
            let Some(item_expr) = source_file.get(item_id).cloned() else {
                continue;
            };

            if let Expr::Return(_) = item_expr {
                // Explicit returns count as a return value (duh)
                let ty = self.infer_node(item_id, env, expected, source_file)?;
                ret_tys.push(ty.clone());
                block_return_ty = Some(ty);
            } else if i == items.len() - 1 {
                // The last item counts as a return value
                let ty = self.infer_node(item_id, env, expected, source_file)?;
                block_return_ty = Some(ty);

                // If we have any explicit returns, we need to constrain equality of this with them
                for ret_ty in &ret_tys {
                    env.constrain_equality(
                        *item_id,
                        block_return_ty.clone().unwrap_or(Ty::Void),
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
        &mut self,
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
        let ret_ty = arms_ty.last().cloned().unwrap_or(Ty::Void);

        Ok(ret_ty)
    }

    fn infer_match_arm(
        &mut self,
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
        Ok(Ty::Void)
    }

    fn infer_member(
        &mut self,
        id: &ExprID,
        env: &mut Environment,
        receiver: &Option<ExprID>,
        member_name: &str,
        expected: &Option<Ty>,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Ty, TypeError> {
        match receiver {
            None => {
                // Unqualified: .some
                // Create a type variable that will be constrained later
                let ret = if let Some(expected) = expected {
                    expected.clone()
                } else {
                    let member_var =
                        env.new_type_variable(TypeVarKind::Member(member_name.to_string()), vec![]);
                    Ty::TypeVar(member_var.clone())
                };

                env.constrain_unqualified_member(*id, member_name.to_string(), ret.clone());

                Ok(ret)
            }
            Some(receiver_id) => {
                // Qualified: Option.some
                let receiver_ty = self.infer_node(receiver_id, env, &None, source_file)?;

                let member_var = Ty::TypeVar(
                    env.new_type_variable(TypeVarKind::Member(member_name.to_string()), vec![]),
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
        &mut self,
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
        &mut self,
        _id: &ExprID,
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
                    env.declare(*symbol_id, scheme)?;
                }
            }
            Pattern::Wildcard => (),
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                // The expected type should be an Enum type
                match expected {
                    Ty::Enum(enum_id, type_args) => {
                        let Some(enum_def) = env.lookup_enum(enum_id).cloned() else {
                            return Err(TypeError::Unknown(format!(
                                "Could not resolve enum with symbol: {enum_id:?}"
                            )));
                        };
                        // Find the variant by name
                        let Some(variant) = enum_def.variants.iter().find(|v| {
                            // Match variant name (comparing the raw string)
                            v.name == *variant_name
                        }) else {
                            return Err(TypeError::UnknownVariant(Name::Raw(
                                variant_name.to_string(),
                            )));
                        };
                        let Ty::EnumVariant(_, values) = &variant.ty else {
                            unreachable!()
                        };
                        // Now we have the variant definition and the concrete type arguments
                        // We need to substitute the enum's type parameters with the actual type args

                        // Create substitution map: enum type param -> concrete type arg
                        let mut substitutions: HashMap<TypeVarID, Ty> = HashMap::new();
                        for (param, arg_ty) in enum_def.type_parameters.iter().zip(type_args.iter())
                        {
                            substitutions.insert(param.type_var.clone(), arg_ty.clone());
                        }

                        // Apply substitutions to get concrete field types
                        let concrete_field_types: Vec<Ty> = values
                            .iter()
                            .map(|field_ty| {
                                ConstraintSolver::<NameResolved>::substitute_ty_with_map(
                                    field_ty,
                                    &substitutions,
                                )
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
                            .unwrap_or(Ty::Void);
                        }
                    }
                    Ty::EnumVariant(_enum_id, values_types) => {
                        // Now match field patterns with their concrete types
                        for (field_pattern, field_ty) in fields.iter().zip(values_types.iter()) {
                            self.infer_node(
                                field_pattern,
                                env,
                                &Some(field_ty.clone()),
                                source_file,
                            )
                            .unwrap_or(Ty::Void);
                        }
                    }
                    Ty::TypeVar(_) => {
                        // The expected type is still a type variable, so we can't look up variant info yet
                        // Just bind any field patterns to fresh type variables
                        for field_pattern in fields {
                            let field_ty = Ty::TypeVar(env.new_type_variable(
                                TypeVarKind::PatternBind(Name::Raw("field".into())),
                                vec![],
                            ));

                            self.infer_node(field_pattern, env, &Some(field_ty), source_file)
                                .unwrap_or(Ty::Void);
                        }
                    }
                    _ => log::error!(
                        "Unhandled pattern variant: {pattern:?}, expected: {expected:?}"
                    ),
                }
            }
        }

        Ok(())
    }
}
