use std::{collections::HashMap, path::PathBuf};

use tracing::trace_span;

use crate::{
    ExprMetaStorage, NameResolved, SymbolID, SymbolTable, Typed,
    compiling::{
        compilation_session::SharedCompilationSession,
        compiled_module::{CompiledModule, ImportedSymbol},
    },
    conformance::Conformance,
    conformance_checker::ConformanceError,
    constraint::Constraint,
    constraint_solver::ConstraintSolver,
    diagnostic::Diagnostic,
    environment::free_type_vars,
    expr_id::ExprID,
    name::{Name, ResolvedName},
    name_resolver::NameResolverError,
    parsed_expr::{self, IncompleteExpr, ParsedExpr, Pattern},
    row::{FieldInfo, Label, RowConstraint, RowSpec},
    semantic_index::ResolvedExpr,
    source_file::SourceFile,
    substitutions::Substitutions,
    synthesis::synthesize_inits,
    token_kind::TokenKind,
    ty::{RowKind, Ty},
    type_def::TypeDef,
    type_var_id::{TypeVarID, TypeVarKind},
    typed_expr,
};

use super::{environment::Environment, typed_expr::TypedExpr};

pub type TypeDefs = HashMap<SymbolID, TypeDef>;
pub type FuncParams = Vec<Ty>;
pub type FuncReturning = Box<Ty>;

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum TypeError {
    Unresolved(String),
    NameResolution(NameResolverError),
    UnknownEnum(Name),
    UnknownVariant(Name),
    Unknown(String),
    UnexpectedType(String, String),
    Mismatch(String, String),
    ArgumentError(String),
    Defer(ConformanceError),
    Handled, // If we've already reported it
    OccursConflict,
    Incomplete(Box<IncompleteExpr>),
    ConformanceError(Vec<ConformanceError>),
    Nonconformance(String, String),
    MemberNotFound(String, String),
}

impl TypeError {
    pub fn message(&self) -> String {
        match self {
            Self::Defer(err) => format!("{err:?}"),
            Self::Unresolved(name) => format!("Unresolved name: {name}"),
            Self::NameResolution(e) => e.message(),
            Self::UnknownEnum(name) => format!("No enum named {}", name.name_str()),
            Self::UnknownVariant(name) => format!("No case named {}", name.name_str()),
            Self::Unknown(err) => format!("Unknown error: {err}"),
            Self::Incomplete(expr) => format!("Incomplete: {expr:?}"),
            Self::UnexpectedType(actual, expected) => {
                format!("Unexpected type: {expected}, expected: {actual}")
            }
            Self::Mismatch(expected, actual) => {
                format!("Type mismatch: {expected}, expected: {actual}")
            }
            Self::Handled => unreachable!("Handled errors should not be displayed"),
            Self::OccursConflict => "Recursive types are not supported".to_string(),
            Self::ArgumentError(message) => message.to_string(),
            Self::Nonconformance(protocol, structname) => {
                format!("{structname} does not conform to the {protocol} protocol")
            }
            Self::MemberNotFound(receiver, name) => {
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
    ty: Ty,
    unbound_vars: Vec<TypeVarID>,
    constraints: Vec<Constraint>,
}

impl Scheme {
    pub fn new(ty: Ty, unbound_vars: Vec<TypeVarID>, constraints: Vec<Constraint>) -> Self {
        Self {
            ty,
            unbound_vars,
            constraints,
        }
    }

    pub fn ty(&self) -> Ty {
        self.ty.clone()
    }

    pub fn unbound_vars(&self) -> Vec<TypeVarID> {
        self.unbound_vars.clone()
    }

    pub fn constraints(&self) -> Vec<Constraint> {
        self.constraints.clone()
    }
}

#[derive(Debug)]
pub struct TypeChecker<'a> {
    pub(crate) symbol_table: &'a mut SymbolTable,
    session: SharedCompilationSession,
    pub(super) path: PathBuf,
    pub(super) meta: &'a ExprMetaStorage,
    pub(super) module_env: &'a HashMap<String, CompiledModule>,
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
    pub fn new(
        session: SharedCompilationSession,
        symbol_table: &'a mut SymbolTable,
        path: PathBuf,
        meta: &'a ExprMetaStorage,
        module_env: &'a HashMap<String, CompiledModule>,
    ) -> Self {
        Self {
            session,
            symbol_table,
            path,
            meta,
            module_env,
        }
    }

    pub fn infer(
        &mut self,
        source_file: &'a mut SourceFile<NameResolved>,
        env: &mut Environment,
    ) -> SourceFile<Typed> {
        self.infer_without_prelude(env, source_file)
    }

    pub fn infer_without_prelude(
        &mut self,
        env: &mut Environment,
        source_file: &'a mut SourceFile<NameResolved>,
    ) -> SourceFile<Typed> {
        synthesize_inits(source_file, self.symbol_table, env);

        let roots = source_file.roots();

        // Just define names for all of the funcs, structs and enums
        if let Err(e) = self.hoist(roots, env)
            && let Ok(mut lock) = self.session.lock()
        {
            let span = if let Some(first_root) = roots.first().map(|r| r.id)
                && let Some(meta) = source_file.meta.borrow().get(&first_root)
            {
                meta.span()
            } else {
                (0, 0)
            };

            lock.add_diagnostic(Diagnostic::typing(source_file.path.clone(), span, e));
        }

        let mut typed_roots = vec![];
        for parsed_expr in roots {
            #[allow(clippy::unwrap_used)]
            match self.infer_node(parsed_expr, env, &None) {
                Ok(typed_expr) => typed_roots.push(typed_expr),
                Err(e) => {
                    let span = if let Some(meta) = source_file.meta.borrow().get(&parsed_expr.id) {
                        meta.span()
                    } else {
                        (0, 0)
                    };

                    if let Ok(mut lock) = self.session.lock() {
                        lock.add_diagnostic(Diagnostic::typing(source_file.path.clone(), span, e))
                    }
                }
            }
        }

        source_file.to_typed(typed_roots, source_file.phase_data.scope_tree.clone())
    }

    pub fn infer_nodes(
        &mut self,
        parsed_exprs: &[ParsedExpr],
        env: &mut Environment,
    ) -> Result<Vec<TypedExpr>, TypeError> {
        let mut result = vec![];
        for parsed_expr in parsed_exprs {
            result.push(self.infer_node(parsed_expr, env, &None)?);
        }
        Ok(result)
    }

    pub fn infer_node(
        &mut self,
        parsed_expr: &ParsedExpr,
        env: &mut Environment,
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        let _s = trace_span!(
            "infer_node",
            expr = crate::formatter::Formatter::format_single_expr(self.meta, parsed_expr)
        )
        .entered();

        let mut ty = match &parsed_expr.expr {
            crate::parsed_expr::Expr::Incomplete(expr_id) => self.handle_incomplete(expr_id),
            crate::parsed_expr::Expr::Import(name) => Ok(TypedExpr {
                id: parsed_expr.id,
                expr: typed_expr::Expr::Import(name.to_string()),
                ty: Ty::Void,
            }),
            crate::parsed_expr::Expr::LiteralTrue => {
                checked_expected(expected, Ty::Bool)?;
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: Ty::Bool,
                    expr: typed_expr::Expr::LiteralTrue,
                })
            }
            crate::parsed_expr::Expr::LiteralFalse => {
                checked_expected(expected, Ty::Bool)?;
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: Ty::Bool,
                    expr: typed_expr::Expr::LiteralFalse,
                })
            }
            crate::parsed_expr::Expr::Loop(cond, body) => {
                self.infer_loop(parsed_expr.id, cond, body, env)
            }
            crate::parsed_expr::Expr::If(condition, consequence, alternative) => self.infer_if(
                parsed_expr.id,
                condition,
                consequence,
                &alternative.as_ref().map(|r| &**r),
                env,
            ),
            crate::parsed_expr::Expr::Call {
                callee,
                type_args,
                args,
            } => self.infer_call(parsed_expr.id, env, callee, type_args, args, expected),
            crate::parsed_expr::Expr::LiteralInt(v) => {
                // checked_expected(expected, Ty::Int)?;
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: Ty::Int,
                    expr: typed_expr::Expr::LiteralInt(v.to_string()),
                })
            }
            crate::parsed_expr::Expr::LiteralFloat(v) => {
                // checked_expected(expected, Ty::Float)?;
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: Ty::Float,
                    expr: typed_expr::Expr::LiteralFloat(v.to_string()),
                })
            }
            crate::parsed_expr::Expr::LiteralString(v) => Ok(TypedExpr {
                id: parsed_expr.id,
                expr: typed_expr::Expr::LiteralString(v.to_string()),
                ty: Ty::string(),
            }),
            crate::parsed_expr::Expr::Assignment(lhs, rhs) => {
                self.infer_assignment(parsed_expr.id, lhs, rhs, env)
            }
            crate::parsed_expr::Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => self.infer_type_repr(
                parsed_expr.id,
                name,
                generics,
                conformances,
                *introduces_type,
                env,
            ),
            crate::parsed_expr::Expr::FuncTypeRepr(args, ret, is_type_parameter) => self
                .infer_func_type_repr(parsed_expr.id, env, args, ret, expected, *is_type_parameter),
            crate::parsed_expr::Expr::TupleTypeRepr(types, is_type_parameter) => {
                self.infer_tuple_type_repr(parsed_expr.id, types, *is_type_parameter, env)
            }
            crate::parsed_expr::Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                captures,
                ..
            } => self.infer_func(
                parsed_expr.id,
                name,
                generics,
                params,
                captures,
                body,
                ret,
                env,
                None,
            ),
            crate::parsed_expr::Expr::Let(name, rhs) => {
                self.infer_let(parsed_expr.id, env, name, rhs, expected)
            }
            crate::parsed_expr::Expr::Variable(name) => {
                self.infer_variable(parsed_expr.id, name, env)
            }
            crate::parsed_expr::Expr::Parameter(name @ Name::Resolved(_, _), param_ty) => {
                self.infer_parameter(parsed_expr.id, name, param_ty, env)
            }
            crate::parsed_expr::Expr::Tuple(types) => self.infer_tuple(parsed_expr.id, types, env),
            crate::parsed_expr::Expr::Unary(op, rhs) => {
                self.infer_unary(parsed_expr.id, op.clone(), rhs, expected, env)
            }
            crate::parsed_expr::Expr::Binary(lhs, op, rhs) => {
                self.infer_binary(parsed_expr.id, lhs, rhs, op, expected, env)
            }
            crate::parsed_expr::Expr::Block(items) => {
                self.infer_block(parsed_expr.id, items, env, expected)
            }
            crate::parsed_expr::Expr::EnumDecl {
                name: Name::Resolved(symbol_id, name_str),
                body,
                generics,
                conformances,
            } => self.infer_enum_decl(
                parsed_expr.id,
                symbol_id,
                name_str.clone(),
                body,
                generics,
                conformances,
                env,
            ),
            crate::parsed_expr::Expr::EnumVariant(name, values) => {
                self.infer_enum_variant(parsed_expr.id, name, values, expected, env)
            }
            crate::parsed_expr::Expr::Match(pattern, items) => {
                self.infer_match(parsed_expr.id, pattern, items, env)
            }
            crate::parsed_expr::Expr::MatchArm(pattern, body) => {
                self.infer_match_arm(parsed_expr.id, pattern, body, expected, env)
            }
            crate::parsed_expr::Expr::PatternVariant(enum_name, variant_name, items) => {
                self.infer_pattern_variant(parsed_expr.id, enum_name, variant_name, items, env)
            }
            crate::parsed_expr::Expr::Member(receiver, member_name) => {
                self.infer_member(parsed_expr.id, receiver, member_name, expected, env)
            }
            crate::parsed_expr::Expr::ParsedPattern(pattern) => {
                self.infer_pattern_expr(parsed_expr.id, parsed_expr, pattern, expected, env)
            }
            crate::parsed_expr::Expr::Return(rhs) => {
                self.infer_return(parsed_expr.id, rhs, env, expected)
            }
            crate::parsed_expr::Expr::LiteralArray(items) => {
                self.infer_array(parsed_expr.id, items, expected, env)
            }
            crate::parsed_expr::Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => self.infer_struct(
                parsed_expr.id,
                name,
                generics,
                conformances,
                body,
                env,
                expected,
            ),
            crate::parsed_expr::Expr::Extend {
                name,
                generics,
                conformances,
                body,
            } => self.infer_extension(
                parsed_expr.id,
                name,
                generics,
                conformances,
                body,
                env,
                expected,
            ),
            crate::parsed_expr::Expr::CallArg { value, .. } => {
                let typed = self.infer_node(value, env, expected)?;
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: typed.ty.clone(),
                    expr: typed_expr::Expr::CallArg {
                        label: None, // We don't care about call labels in the type system
                        value: Box::new(typed),
                    },
                })
            }
            crate::parsed_expr::Expr::Init(Some(struct_id), func_id) => {
                self.infer_init(parsed_expr.id, struct_id, func_id, env)
            }
            crate::parsed_expr::Expr::Property {
                name,
                type_repr,
                default_value,
            } => self.infer_property(parsed_expr.id, name, type_repr, default_value, env),
            crate::parsed_expr::Expr::Break => Ok(TypedExpr {
                id: parsed_expr.id,
                expr: typed_expr::Expr::Break,
                ty: Ty::Void,
            }),
            crate::parsed_expr::Expr::ProtocolDecl {
                name,
                associated_types,
                conformances,
                body,
            } => self.infer_protocol(
                parsed_expr.id,
                name,
                associated_types,
                conformances,
                body,
                env,
            ),
            crate::parsed_expr::Expr::FuncSignature {
                name,
                params,
                generics,
                ret,
                ..
            } => {
                let params = self.infer_nodes(params, env)?;
                let generics = self.infer_nodes(generics, env)?;
                let ret = self.infer_node(ret, env, &None)?;
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: Ty::Func(
                        params.iter().map(|p| p.ty.clone()).collect(),
                        Box::new(ret.ty.clone()),
                        generics.iter().map(|g| g.ty.clone()).collect(),
                    ),
                    expr: typed_expr::Expr::FuncSignature {
                        name: name.resolved()?,
                        params,
                        generics,
                        ret: Box::new(ret),
                    },
                })
            }
            crate::parsed_expr::Expr::RecordLiteral(fields) => {
                self.infer_record_literal(parsed_expr.id, fields, expected, env)
            }
            crate::parsed_expr::Expr::RecordField { label, value } => {
                self.infer_record_field(parsed_expr.id, label, value, expected, env)
            }
            crate::parsed_expr::Expr::RecordTypeRepr {
                fields,
                row_var,
                introduces_type,
            } => self.infer_record_type_repr(
                parsed_expr.id,
                fields,
                row_var,
                *introduces_type,
                expected,
                env,
            ),
            crate::parsed_expr::Expr::RecordTypeField { label, ty } => {
                self.infer_record_type_field(parsed_expr.id, label, ty, expected, env)
            }
            crate::parsed_expr::Expr::RowVariable(name) => {
                self.infer_row_variable(parsed_expr.id, name, expected, env)
            }
            crate::parsed_expr::Expr::Spread(expr) => {
                self.infer_spread(parsed_expr.id, expr, expected, env)
            }
            _ => Err(TypeError::Unknown(format!(
                "Don't know how to type check {parsed_expr:?}"
            ))),
        };

        match &ty {
            Ok(_ty) => {}
            Err(e) => {
                tracing::error!("error inferring: {e:?}");
                if let Ok(mut lock) = self.session.lock() {
                    let span = if let Some(meta) = self.meta.get(&parsed_expr.id) {
                        meta.span()
                    } else {
                        (0, 0)
                    };

                    lock.add_diagnostic(Diagnostic::typing(self.path.clone(), span, e.clone()));
                }
                ty = Err(TypeError::Handled);
            }
        }

        ty
    }

    #[tracing::instrument(level = "DEBUG", skip(self,))]
    fn handle_incomplete(&mut self, expr: &IncompleteExpr) -> Result<TypedExpr, TypeError> {
        Err(TypeError::OccursConflict)
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_protocol(
        &mut self,
        id: ExprID,
        name: &Name,
        associated_types: &[ParsedExpr],
        conformances: &[ParsedExpr],
        body: &ParsedExpr,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        env.start_scope();

        let mut inferred_associated_types: Vec<TypedExpr> = vec![];
        for generic in associated_types {
            inferred_associated_types.push(self.infer_node(generic, env, &None)?);
        }

        let Name::Resolved(symbol_id, name_str) = name else {
            return Err(TypeError::Unresolved(name.name_str()));
        };
        // Protocols are represented as Row types
        let ty = Ty::protocol_type(
            *symbol_id,
            inferred_associated_types
                .iter()
                .map(|t| t.ty.clone())
                .collect(),
        );

        env.selfs.push(ty.clone());
        let body = self.infer_node(body, env, &None)?;
        env.selfs.pop();
        env.end_scope();

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::ProtocolDecl {
                name: ResolvedName(*symbol_id, name_str.to_string()),
                associated_types: inferred_associated_types.clone(),
                conformances: self.infer_nodes(conformances, env)?,
                body: Box::new(body),
            },
            ty,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_property(
        &mut self,
        id: ExprID,
        name: &Name,
        type_repr: &Option<Box<ParsedExpr>>,
        default_value: &Option<Box<ParsedExpr>>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let type_repr = type_repr
            .as_ref()
            .map(|expr| self.infer_node(expr, env, &None))
            .transpose()?;
        let default_value = default_value
            .as_ref()
            .map(|expr| self.infer_node(expr, env, &None))
            .transpose()?;

        let ty = match (&type_repr, &default_value) {
            (Some(type_repr), Some(default_value)) => {
                env.constrain(Constraint::Equality(
                    id,
                    type_repr.ty.clone(),
                    default_value.ty.clone(),
                ));
                type_repr.ty.clone()
            }
            (None, Some(default_value)) => default_value.ty.clone(),
            (Some(type_repr), None) => type_repr.ty.clone(),
            (None, None) => env.placeholder(&id, name.name_str(), &name.symbol_id()?, vec![]),
        };

        Ok(TypedExpr {
            id,
            ty,
            expr: typed_expr::Expr::Property {
                name: name.resolved()?,
                type_repr: type_repr.map(Box::new),
                default_value: default_value.map(Box::new),
            },
        })
    }

    #[allow(clippy::too_many_arguments)]
    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_enum_decl(
        &mut self,
        id: ExprID,
        enum_id: &SymbolID,
        name: String,
        body: &ParsedExpr,
        conformances: &[ParsedExpr],
        generics: &[ParsedExpr],
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let scheme = env.lookup_symbol(enum_id)?;
        let ty = scheme.ty.clone();

        env.start_scope();
        env.selfs.push(ty.clone());
        let conformances = self.infer_nodes(conformances, env)?;
        let generics = self.infer_nodes(generics, env)?;
        let body = Box::new(self.infer_node(body, env, &Some(ty.clone()))?);
        env.selfs.pop();

        Ok(TypedExpr {
            id,
            ty: ty.clone(),
            expr: typed_expr::Expr::EnumDecl {
                name: ResolvedName(*enum_id, name),
                conformances,
                generics,
                body,
            },
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected,))]
    fn infer_enum_variant(
        &mut self,
        id: ExprID,
        name: &Name,
        values: &[ParsedExpr],
        expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let Some(Ty::Row {
            nominal_id: Some(enum_id),
            generics,
            kind: RowKind::Enum,
            ..
        }) = env.selfs.last().cloned()
        else {
            unreachable!(
                "should always be called with expected = Enum, got: {expected:?}, self: {:?}",
                env.selfs.last()
            );
        };
        let values = self.infer_nodes(values, env)?;

        // The type of a variant declaration is either:
        // - A function from the variant's parameters to the enum type (if it has parameters)
        // - The enum type itself (if it has no parameters)
        let ty = if values.is_empty() {
            Ty::enum_type(enum_id, generics)
        } else {
            Ty::Func(
                values.iter().map(|v| v.ty.clone()).collect(),
                Box::new(Ty::enum_type(enum_id, generics)),
                vec![], // No generic parameters on the function itself
            )
        };

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::EnumVariant(ResolvedName(enum_id, name.name_str()), values),
            ty,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_parameter(
        &mut self,
        id: ExprID,
        name: &Name,
        param_ty: &Option<Box<ParsedExpr>>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let param_ty = if let Some(param_ty) = &param_ty {
            Some(Box::new(self.infer_node(param_ty, env, &None)?))
        } else {
            None
        };

        let ty = param_ty.as_ref().map(|t| t.ty.clone()).unwrap_or_else(|| {
            Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncParam(name.name_str()), id))
        });

        // Parameters are monomorphic inside the function body
        let constraints = env
            .constraints()
            .iter()
            .filter(|c| c.contains_ty(&ty))
            .cloned()
            .collect();
        let scheme = Scheme::new(ty.clone(), vec![], constraints);
        env.declare(name.symbol_id()?, scheme)?;

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Parameter(
                ResolvedName(name.symbol_id()?, name.name_str()),
                param_ty,
            ),
            ty,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env,))]
    fn infer_init(
        &mut self,
        id: ExprID,
        struct_id: &SymbolID,
        func_expr: &ParsedExpr,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let scheme = env.lookup_symbol(struct_id)?.clone();
        let overridden_ret = env.instantiate(&scheme);

        let ParsedExpr {
            id: func_id,
            expr:
                parsed_expr::Expr::Func {
                    // Initializers share their struct's symbol ID for convenience during
                    // name resolution. However, using that ID when inferring the function
                    // would overwrite the struct's own type scheme. The initializer does not
                    // need a named symbol during inference, so we explicitly ignore its
                    // resolved name here.
                    name: _,
                    generics,
                    params,
                    body,
                    ret,
                    captures,
                    ..
                },
        } = func_expr
        else {
            return Err(TypeError::Unknown(format!(
                "Did not get func for init: {func_expr:?}"
            )));
        };

        // TODO: Add a test to make sure ret isn't set (it should never be for inits)

        let inferred = self.infer_func(
            *func_id,
            &None,
            generics,
            params,
            captures,
            body,
            ret,
            env,
            Some(&overridden_ret),
        )?;

        let params = match &inferred.ty {
            Ty::Func(params, _, _) => params.clone(),
            Ty::Closure {
                func: box Ty::Func(params, _, _),
                ..
            } => params.clone(),
            _ => {
                return Err(TypeError::Unknown(format!(
                    "Did not get init func, got: {inferred:?}"
                )));
            }
        };

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Init(*struct_id, inferred.clone().into()),
            ty: Ty::Init(*struct_id, params.clone()),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env,))]
    pub(super) fn infer_method(
        &mut self,
        id: ExprID,
        func_expr: &ParsedExpr,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let ParsedExpr {
            id: func_id,
            expr:
                parsed_expr::Expr::Func {
                    // Initializers share their struct's symbol ID for convenience during
                    // name resolution. However, using that ID when inferring the function
                    // would overwrite the struct's own type scheme. The initializer does not
                    // need a named symbol during inference, so we explicitly ignore its
                    // resolved name here.
                    name: _,
                    generics,
                    params,
                    body,
                    ret,
                    captures,
                    ..
                },
        } = func_expr
        else {
            return Err(TypeError::Unknown(format!(
                "Did not get func for init: {func_expr:?}"
            )));
        };

        let func = self.infer_func(
            *func_id, &None, generics, params, captures, body, ret, env, None,
        )?;

        #[allow(clippy::expect_used)]
        let self_ty = env.selfs.last().expect("No self found for method");

        Ok(TypedExpr {
            id,
            expr: func.expr,
            ty: Ty::Method {
                self_ty: Box::new(self_ty.clone()),
                func: Box::new(func.ty),
            },
        })
    }

    #[allow(clippy::too_many_arguments)]
    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
    fn infer_extension(
        &mut self,
        id: ExprID,
        name: &Name,
        generics: &[ParsedExpr],
        conformances: &[ParsedExpr],
        body: &ParsedExpr,
        env: &mut Environment,
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        let mut inferred_generics: Vec<TypedExpr> = vec![];
        for generic in generics {
            inferred_generics.push(self.infer_node(generic, env, expected)?.clone());
        }

        let Name::Resolved(symbol_id, name_str) = name else {
            return Err(TypeError::Unresolved(name.name_str()));
        };

        let ty = Ty::struct_type(
            *symbol_id,
            inferred_generics.iter().map(|t| t.ty.clone()).collect(),
        );

        env.selfs.push(ty.clone());
        let body = Box::new(self.infer_node(body, env, &None)?);
        env.selfs.pop();

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Extend {
                name: ResolvedName(*symbol_id, name_str.to_string()),
                generics: inferred_generics,
                conformances: self.infer_nodes(conformances, env)?,
                body,
            },
            ty,
        })
    }

    #[allow(clippy::too_many_arguments)]
    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
    fn infer_struct(
        &mut self,
        id: ExprID,
        name: &Name,
        generics: &[ParsedExpr],
        conformances: &[ParsedExpr],
        body: &ParsedExpr,
        env: &mut Environment,
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        let mut inferred_generics: Vec<TypedExpr> = vec![];
        for generic in generics {
            inferred_generics.push(self.infer_node(generic, env, expected)?.clone());
        }

        let Name::Resolved(symbol_id, name_str) = name else {
            return Err(TypeError::Unresolved(name.name_str()));
        };

        let ty = Ty::struct_type(
            *symbol_id,
            inferred_generics.iter().map(|t| t.ty.clone()).collect(),
        );

        env.selfs.push(ty.clone());
        let body = self.infer_node(body, env, &None)?;
        env.selfs.pop();

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Struct {
                name: ResolvedName(*symbol_id, name_str.to_string()),
                generics: inferred_generics,
                conformances: self.infer_nodes(conformances, env)?,
                body: Box::new(body),
            },
            ty,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected,))]
    fn infer_array(
        &mut self,
        id: ExprID,
        items: &[ParsedExpr],
        expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let mut typed_items: Vec<TypedExpr> = vec![];
        for i in items {
            typed_items.push(self.infer_node(i, env, expected)?);
        }

        // TODO: error when the tys don't match
        let ty = typed_items
            .iter()
            .last()
            .map(|t| t.ty.clone())
            .unwrap_or_else(|| Ty::TypeVar(env.new_type_variable(TypeVarKind::Element, id)));

        Ok(TypedExpr {
            id,
            ty: Ty::struct_type(SymbolID::ARRAY, vec![ty]),
            expr: typed_expr::Expr::LiteralArray(typed_items),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected,))]
    fn infer_return(
        &mut self,
        id: ExprID,
        rhs: &Option<Box<ParsedExpr>>,
        env: &mut Environment,
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        let ret = if let Some(rhs_id) = rhs {
            Some(Box::new(self.infer_node(rhs_id, env, expected)?))
        } else {
            None
        };

        Ok(TypedExpr {
            id,
            ty: ret.as_ref().map(|r| r.ty.clone()).unwrap_or(Ty::Void),
            expr: typed_expr::Expr::Return(ret),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_loop(
        &mut self,
        id: ExprID,
        cond: &Option<Box<ParsedExpr>>,
        body: &ParsedExpr,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let cond = if let Some(cond) = cond {
            let cond = self.infer_node(cond, env, &Some(Ty::Bool))?;
            env.constrain(Constraint::Equality(id, cond.ty.clone(), Ty::Bool));
            Some(Box::new(cond))
        } else {
            None
        };

        Ok(TypedExpr {
            id,
            ty: Ty::Void,
            expr: typed_expr::Expr::Loop(cond, Box::new(self.infer_node(body, env, &None)?)),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_if(
        &mut self,
        id: ExprID,
        condition: &ParsedExpr,
        consequence: &ParsedExpr,
        alternative: &Option<&ParsedExpr>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let condition = self.infer_node(condition, env, &Some(Ty::Bool))?;

        env.constrain(Constraint::Equality(id, condition.ty.clone(), Ty::Bool));

        let consequence = self.infer_node(consequence, env, &None)?;
        let alt = if let Some(alternative) = alternative {
            let alternative = self.infer_node(alternative, env, &None)?;
            env.constrain(Constraint::Equality(
                alternative.id,
                consequence.ty.clone(),
                alternative.ty.clone(),
            ));
            Some(Box::new(alternative.clone()))
        } else {
            None
        };

        Ok(TypedExpr {
            id,
            ty: if alt.is_some() {
                consequence.ty.clone()
            } else {
                consequence.ty.optional()
            },
            expr: typed_expr::Expr::If(Box::new(condition), Box::new(consequence), alt),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected,))]
    #[allow(clippy::too_many_arguments)]
    fn infer_call(
        &mut self,
        id: ExprID,
        env: &mut Environment,
        callee: &ParsedExpr,
        type_args: &[ParsedExpr],
        args: &[ParsedExpr],
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        let mut ret_var = if let Some(expected) = expected {
            expected.clone()
        } else {
            // Avoid borrow checker issue by creating the type variable before any borrows
            let call_return_var = env.new_type_variable(TypeVarKind::CallReturn, id);
            Ty::TypeVar(call_return_var)
        };

        let mut inferred_type_args = vec![];
        for type_arg in type_args {
            inferred_type_args.push(self.infer_node(type_arg, env, &None)?);
        }

        let mut arg_tys = vec![];
        for arg in args {
            let ty = self.infer_node(arg, env, &None)?;
            arg_tys.push(ty);
        }

        let callee = self.infer_node(callee, env, expected)?;

        match &callee.expr {
            // Handle struct initialization
            typed_expr::Expr::Variable(ResolvedName(symbol_id, _name_str))
                if env.is_struct_symbol(symbol_id) =>
            {
                let Some(struct_def) = env.lookup_struct(symbol_id).cloned() else {
                    return Err(TypeError::Unknown(format!(
                        "Could not resolve symbol {symbol_id:?}"
                    )));
                };

                let placeholder = env.placeholder(
                    &callee.id,
                    format!("init({symbol_id:?})"),
                    symbol_id,
                    vec![],
                );

                // If there aren't explicit type params specified, create some placeholders. I guess for now
                // if there are _some_ we'll just use positional values?
                let mut type_args = vec![];

                if !struct_def.type_parameters.is_empty() {
                    for (i, type_arg) in struct_def.type_parameters.iter().enumerate() {
                        type_args.push(if i < inferred_type_args.len() {
                            inferred_type_args[i].ty.clone()
                        } else {
                            env.placeholder(
                                &id,
                                format!("Call Placeholder {type_arg:?}"),
                                &type_arg.id,
                                vec![],
                            )
                        });
                    }
                }

                let constraints = env
                    .constraints()
                    .iter()
                    .filter(|c| {
                        struct_def
                            .canonical_type_parameters()
                            .iter()
                            .any(|p| c.contains_ty(p))
                    })
                    .cloned()
                    .collect::<Vec<Constraint>>();

                ret_var = env.instantiate(&Scheme::new(
                    Ty::struct_type(*symbol_id, type_args.clone()),
                    struct_def.canonical_type_variables(),
                    constraints,
                ));

                env.constrain(Constraint::InitializerCall {
                    expr_id: callee.id,
                    initializes_id: *symbol_id,
                    args: arg_tys.iter().map(|a| a.ty.clone()).collect(),
                    type_args,
                    func_ty: placeholder.clone(),
                    result_ty: ret_var.clone(),
                });
            }
            _ => {
                let _s = tracing::trace_span!("non-struct call").entered();
                let expected_callee_ty = Ty::Func(
                    arg_tys.iter().map(|a| a.ty.clone()).collect(),
                    Box::new(ret_var.clone()),
                    inferred_type_args.iter().map(|a| a.ty.clone()).collect(),
                );

                env.constrain(Constraint::Equality(
                    callee.id,
                    callee.ty.clone(),
                    expected_callee_ty,
                ));
            }
        };

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Call {
                callee: Box::new(callee),
                type_args: inferred_type_args,
                args: arg_tys,
            },
            ty: ret_var,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_assignment(
        &mut self,
        id: ExprID,
        lhs: &ParsedExpr,
        rhs: &ParsedExpr,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let rhs_ty = self.infer_node(rhs, env, &None)?;

        // Expect lhs to be the same as rhs
        let lhs_ty = self.infer_node(lhs, env, &Some(rhs_ty.ty.clone()))?;

        env.constrain(Constraint::Equality(
            rhs.id,
            rhs_ty.ty.clone(),
            lhs_ty.ty.clone(),
        ));

        Ok(TypedExpr {
            id,
            ty: rhs_ty.ty.clone(),
            expr: typed_expr::Expr::Assignment(Box::new(lhs_ty), Box::new(rhs_ty)),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    #[allow(clippy::too_many_arguments)]
    fn infer_type_repr(
        &mut self,
        id: ExprID,
        name: &Name,
        generics: &[ParsedExpr],
        conformances: &[ParsedExpr],
        introduces_type: bool,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let (symbol_id, name_str) = match name {
            Name::SelfType => match env.selfs.last() {
                Some(Ty::Row {
                    nominal_id: Some(symbol_id),
                    ..
                }) => (*symbol_id, "Self".to_string()),
                _ => {
                    return Err(TypeError::Unresolved(format!(
                        "Unable to get Self for {name:?}",
                    )));
                }
            },
            _ => (name.symbol_id()?, name.name_str()),
        };

        // If it's a type parameter, it's defining a generic type
        if introduces_type {
            let mut unbound_vars = vec![];
            let mut conformance_data = vec![];
            let mut typed_conformances = vec![];

            for conformance in conformances {
                let typed_conformance = self.infer_node(conformance, env, &None)?;
                // Protocols are now represented as Row types
                let (protocol_id, associated_types) = match &typed_conformance.ty {
                    Ty::Row {
                        nominal_id: Some(id),
                        generics,
                        kind: RowKind::Protocol,
                        ..
                    } => (*id, generics.clone()),
                    Ty::Row { kind, .. } => {
                        return Err(TypeError::Unknown(format!(
                            "{typed_conformance:?} is not a protocol (kind: {kind:?})"
                        )));
                    }
                    _ => {
                        return Err(TypeError::Unknown(format!(
                            "{typed_conformance:?} is not a protocol",
                        )));
                    }
                };

                unbound_vars.extend(associated_types.iter().filter_map(|t| {
                    if let Ty::TypeVar(var) = t {
                        Some(var.clone())
                    } else {
                        None
                    }
                }));

                typed_conformances.push(typed_conformance.clone());
                conformance_data.push((conformance.id, protocol_id, associated_types));
            }

            let ref ty @ Ty::TypeVar(ref type_var_id) =
                env.placeholder(&id, name.name_str(), &symbol_id, vec![])
            else {
                unreachable!()
            };

            let mut constraints = vec![];

            for (id, protocol_id, associated_types) in conformance_data {
                let constraint = Constraint::ConformsTo {
                    expr_id: id,
                    ty: ty.clone(),
                    conformance: Conformance::new(protocol_id, associated_types.to_vec()),
                };

                tracing::info!("Constraining type repr {constraint:?}");
                constraints.push(constraint.clone());
                env.constrain(constraint)
            }

            unbound_vars.push(type_var_id.clone());

            let scheme = Scheme::new(ty.clone(), unbound_vars, constraints);

            env.declare(symbol_id, scheme.clone())?;

            return Ok(TypedExpr {
                id,
                expr: typed_expr::Expr::TypeRepr {
                    name: ResolvedName(symbol_id, name_str.to_string()),
                    generics: self.infer_nodes(generics, env)?,
                    conformances: typed_conformances,
                    introduces_type: true,
                },
                ty: scheme.ty.clone(),
            });
        }

        // It's not type params, it's type args that already exist
        // If there are no generic arguments (`let x: Int`), we are done.
        if generics.is_empty() {
            let ty = if name == &Name::SelfType {
                Ty::TypeVar(env.new_type_variable(TypeVarKind::SelfVar(symbol_id), id))
            } else {
                env.ty_for_symbol(&id, name.name_str(), &symbol_id, &[])
            };

            return Ok(TypedExpr {
                id,
                expr: typed_expr::Expr::TypeRepr {
                    name: ResolvedName(symbol_id, name_str.to_string()),
                    generics: vec![],
                    conformances: vec![],
                    introduces_type: false,
                },
                ty,
            });
        }

        let ty_scheme = env.lookup_symbol(&symbol_id)?.clone();
        let mut substitutions = Substitutions::default();

        let mut typed_generics = vec![];
        for (var, generic) in ty_scheme.unbound_vars.iter().zip(generics) {
            // Recursively get arg_ty
            let typed_generic = self.infer_node(generic, env, &None)?;
            substitutions.insert(var.clone(), typed_generic.ty.clone());
            typed_generics.push(typed_generic);
        }

        let instantiated = env.instantiate_with_args(&ty_scheme, substitutions.clone());

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::TypeRepr {
                name: ResolvedName(symbol_id, name_str.to_string()),
                generics: typed_generics,
                conformances: vec![],
                introduces_type: false,
            },
            ty: instantiated,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected,))]
    fn infer_func_type_repr(
        &mut self,
        id: ExprID,
        env: &mut Environment,
        args: &[ParsedExpr],
        ret: &ParsedExpr,
        expected: &Option<Ty>,
        introduces_type: bool,
    ) -> Result<TypedExpr, TypeError> {
        let mut inferred_args = vec![];
        let mut inferred_arg_tys = vec![];
        for arg in args {
            let inferred = self.infer_node(arg, env, expected)?;
            inferred_arg_tys.push(inferred.ty.clone());
            inferred_args.push(inferred);
        }

        let inferred_ret = self.infer_node(ret, env, expected)?;
        let ty = Ty::Func(inferred_arg_tys, Box::new(inferred_ret.ty.clone()), vec![]);
        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::FuncTypeRepr(
                inferred_args,
                Box::new(inferred_ret),
                introduces_type,
            ),
            ty,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_tuple_type_repr(
        &mut self,
        id: ExprID,
        types: &Vec<ParsedExpr>,
        introduces_type: bool,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let mut typed_exprs = vec![];
        let mut tys = vec![];
        for t in types {
            let typed = self.infer_node(t, env, &None)?;
            tys.push(typed.ty.clone());
            typed_exprs.push(typed);
        }

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::TupleTypeRepr(typed_exprs, introduces_type),
            ty: Ty::Tuple(tys),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, generics, params, body, ret))]
    #[allow(clippy::too_many_arguments)]
    fn infer_func(
        &mut self,
        id: ExprID,
        name: &Option<Name>,
        generics: &[ParsedExpr],
        params: &[ParsedExpr],
        captures: &[SymbolID],
        body: &ParsedExpr,
        ret: &Option<Box<ParsedExpr>>,
        env: &mut Environment,
        override_ret: Option<&Ty>,
    ) -> Result<TypedExpr, TypeError> {
        env.start_scope();

        if let Some(Name::Resolved(symbol_id, _)) = name
            && let Ok(scheme) = env.lookup_symbol(symbol_id).cloned()
        {
            env.declare(*symbol_id, scheme.clone())?;
        };

        let mut inferred_generics = vec![];
        for generic in generics {
            if let parsed_expr::Expr::TypeRepr {
                name: Name::Resolved(_symbol_id, _),
                ..
            } = generic.expr
            {
                let _s = trace_span!("infer_func generic").entered();
                let ty = self.infer_node(generic, env, &None)?;
                inferred_generics.push(ty.clone());
            } else {
                return Err(TypeError::Unresolved(
                    "could not resolve generic symbol".into(),
                ));
            }
        }

        let annotated_ret_ty = if let Some(ret) = ret {
            Some(self.infer_node(ret, env, &None)?)
        } else {
            None
        };

        let mut param_vars: Vec<TypedExpr> = vec![];
        for param in params.iter() {
            let param_ty = self.infer_node(param, env, &None)?;
            param_vars.push(param_ty);
        }

        tracing::info!("Annotated ret ty: {annotated_ret_ty:?}");
        let ret_ty = self.infer_node(body, env, &None)?;

        if let Some(annotated_ret_ty) = &annotated_ret_ty
            && let Some(ret_id) = ret
        {
            env.constrain(Constraint::Equality(
                ret_id.id,
                ret_ty.ty.clone(),
                annotated_ret_ty.ty.clone(),
            ));
        }

        env.end_scope();

        let func_ty = Ty::Func(
            param_vars.iter().map(|p| p.ty.clone()).collect(),
            Box::new(override_ret.cloned().unwrap_or(ret_ty.ty.clone())),
            inferred_generics.iter().map(|p| p.ty.clone()).collect(),
        );
        let inferred_ty = if captures.is_empty() {
            func_ty
        } else {
            Ty::Closure {
                func: func_ty.into(),
                captures: captures.to_vec(),
            }
        };

        if let Some(Name::Resolved(symbol_id, _)) = name {
            // During hoisting we already declared a scheme for this function.
            // Avoid overwriting it here so that the previously solved type
            // (potentially including protocol-associated information) is
            // preserved for later instantiations.
            if env.lookup_symbol(symbol_id).is_err() {
                let new_scheme = Scheme::new(
                    inferred_ty.clone(),
                    free_type_vars(&inferred_ty).into_iter().collect(),
                    vec![],
                );

                env.declare(*symbol_id, new_scheme)?;
            }
        }

        Ok(TypedExpr {
            id,
            ty: inferred_ty,
            expr: typed_expr::Expr::Func {
                name: name.as_ref().and_then(|n| n.resolved().ok()),
                generics: inferred_generics,
                params: param_vars,
                body: Box::new(ret_ty),
                ret: annotated_ret_ty.map(Box::new),
                captures: captures.to_vec(),
            },
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
    fn infer_let(
        &mut self,
        id: ExprID,
        env: &mut Environment,
        name: &Name,
        rhs: &Option<Box<ParsedExpr>>,
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        let (typed_rhs, ty) = if let Some(rhs) = rhs {
            let typed = self.infer_node(rhs, env, &None)?;
            let ty = typed.ty.clone();
            (Some(Box::new(typed)), ty)
        } else if let Some(expected) = expected {
            (None, expected.clone())
        } else {
            (
                None,
                Ty::TypeVar(env.new_type_variable(TypeVarKind::Let, id)),
            )
        };

        let scheme = Scheme::new(ty.clone(), vec![], vec![]);
        env.declare(name.symbol_id()?, scheme)?;

        Ok(TypedExpr {
            id,
            ty,
            expr: typed_expr::Expr::Let(name.resolved()?, typed_rhs),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_variable(
        &self,
        id: ExprID,
        name: &Name,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let ty = match name {
            Name::Imported(_, imported_symbol) => {
                if let Some(ty) = self.import_ty(imported_symbol) {
                    ty
                } else {
                    return Err(TypeError::Unknown(format!(
                        "No type found for imported symbol: {imported_symbol:?}\nEnv:{:?}",
                        self.module_env
                    )));
                }
            }
            Name::_Self(_sym) => {
                if let Some(self_) = env.selfs.last() {
                    match self_ {
                        Ty::Row {
                            nominal_id: Some(symbol_id),
                            kind: RowKind::Protocol,
                            ..
                        } => {
                            Ty::TypeVar(env.new_type_variable(TypeVarKind::SelfVar(*symbol_id), id))
                        }
                        Ty::Row { .. } => self_.clone(),
                        _ => self_.clone(),
                    }
                } else {
                    return Err(TypeError::Unknown(format!(
                        "No value found for `self`: {name:?}. selfs: {:?}",
                        env.selfs
                    )));
                }
            }
            Name::Resolved(symbol_id, _) => {
                let scheme = env.lookup_symbol(symbol_id)?.clone();

                match scheme.ty() {
                    Ty::TypeVar(ref tv)
                        if matches!(
                            tv.kind,
                            TypeVarKind::CanonicalTypeParameter(_) | TypeVarKind::Placeholder(_)
                        ) =>
                    {
                        scheme.ty()
                    }
                    _ => env.instantiate(&scheme),
                }
            }
            Name::Raw(name_str) => return Err(TypeError::Unresolved(name_str.clone())),
            Name::SelfType => env
                .selfs
                .last()
                .cloned()
                .ok_or(TypeError::Unknown("No type found for Self".to_string()))?,
        };

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Variable(name.resolved()?),
            ty,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_tuple(
        &mut self,
        id: ExprID,
        types: &[ParsedExpr],
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        if types.len() == 1 {
            // If it's a single element, don't treat it as a tuple
            return self.infer_node(&types[0], env, &None);
        }

        let mut tys = vec![];
        let mut inferred_types: Vec<TypedExpr> = vec![];
        for t in types {
            let typed = self.infer_node(t, env, &None)?;
            let ty = typed.ty.clone();
            inferred_types.push(typed);
            tys.push(ty);
        }

        let ty = Ty::Tuple(tys);
        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Tuple(inferred_types),
            ty,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
    fn infer_unary(
        &mut self,
        id: ExprID,
        token_kind: TokenKind,
        rhs: &ParsedExpr,
        expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let typed = self.infer_node(rhs, env, expected)?;
        let ty = typed.ty.clone();
        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Unary(token_kind, Box::new(typed)),
            ty,
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
    #[allow(clippy::too_many_arguments)]
    fn infer_binary(
        &mut self,
        id: ExprID,
        lhs_id: &ParsedExpr,
        rhs_id: &ParsedExpr,
        op: &TokenKind,
        expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let lhs = self.infer_node(lhs_id, env, &None)?;
        let rhs = self.infer_node(rhs_id, env, &None)?;

        use TokenKind::*;
        let ret_ty = match op {
            Plus => {
                let ret_ty = expected.clone().unwrap_or_else(|| {
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::BinaryOperand(op.clone()), id))
                });
                env.constrain(Constraint::ConformsTo {
                    expr_id: id,
                    ty: lhs.ty.clone(),
                    conformance: Conformance {
                        protocol_id: SymbolID::ADD,
                        associated_types: vec![rhs.ty.clone(), ret_ty.clone()],
                    },
                });

                ret_ty
            }

            // Bool ops
            EqualsEquals => Ty::Bool,
            BangEquals => Ty::Bool,
            Greater => Ty::Bool,
            GreaterEquals => Ty::Bool,
            Less => Ty::Bool,
            LessEquals => Ty::Bool,

            // Same type ops
            _ => {
                env.constrain(Constraint::Equality(
                    lhs_id.id,
                    lhs.ty.clone(),
                    rhs.ty.clone(),
                ));
                lhs.ty.clone()
            }
        };

        Ok(TypedExpr {
            id,
            ty: ret_ty,
            expr: typed_expr::Expr::Binary(Box::new(lhs), op.clone(), Box::new(rhs)),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, items, expected))]
    fn infer_block(
        &mut self,
        id: ExprID,
        items: &[ParsedExpr],
        env: &mut Environment,
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        env.start_scope();
        // self.hoist(&items, env)?;

        let mut block_return_ty = expected.clone();
        let mut ret_tys = vec![];
        let mut typed_items = vec![];

        for (i, item) in items.iter().enumerate() {
            let typed_item = self.infer_node(item, env, &None)?;
            let ty = typed_item.ty.clone();
            typed_items.push(typed_item);

            if let parsed_expr::Expr::Return(_) = item.expr {
                // Explicit returns count as a return value (duh)
                ret_tys.push(ty.clone());
                block_return_ty = Some(ty);
            } else if i == items.len() - 1 {
                // The last item counts as a return value
                block_return_ty = Some(ty);

                // If we have any explicit returns, we need to constrain equality of this with them
                for ret_ty in &ret_tys {
                    env.constrain(Constraint::Equality(
                        item.id,
                        block_return_ty.clone().unwrap_or(Ty::Void),
                        ret_ty.clone(),
                    ));
                }
            }
        }

        env.end_scope();

        Ok(TypedExpr {
            id,
            ty: block_return_ty.unwrap_or(Ty::Void),
            expr: typed_expr::Expr::Block(typed_items),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_match(
        &mut self,
        id: ExprID,
        pattern: &ParsedExpr,
        arms: &[ParsedExpr],
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let pattern_ty = self.infer_node(pattern, env, &None)?;
        let mut typed_arms = vec![];
        let mut arm_tys = vec![];
        let mut patterns = vec![];

        for arm in arms {
            let typed = self.infer_node(arm, env, &Some(pattern_ty.ty.clone()))?;
            let ty = typed.ty.clone();
            arm_tys.push(ty);

            // Extract pattern from the typed arm
            if let typed_expr::Expr::MatchArm(ref pattern_expr, _) = typed.expr
                && let Some(pattern) = self.extract_pattern_from_typed_expr(pattern_expr)
            {
                patterns.push(pattern);
            }

            typed_arms.push(typed);
        }

        let ret_ty = arm_tys.first().cloned().unwrap_or(Ty::Void);

        // Make sure the return type is the same for all arms
        if arm_tys.len() > 1 {
            for (i, arm_ty) in arm_tys[1..].iter().enumerate() {
                env.constrain(Constraint::Equality(
                    arms[i + 1].id,
                    ret_ty.clone(),
                    arm_ty.clone(),
                ));
            }
        }

        // Check exhaustiveness
        use crate::type_checking::exhaustiveness_integration::check_match_exhaustiveness;

        let check_ty = pattern_ty.ty.clone();

        // Store match information for deferred exhaustiveness checking
        env.defer_exhaustiveness_check(id, pattern_ty.ty.clone(), patterns.clone());

        // For now, only check exhaustiveness immediately for resolved types
        let should_check = !matches!(&check_ty, Ty::TypeVar(_));

        if should_check && let Err(msg) = check_match_exhaustiveness(env, &check_ty, &patterns) {
            // Add diagnostic instead of failing type checking
            if let Ok(mut lock) = self.session.lock() {
                let span = if let Some(meta) = self.meta.get(&id) {
                    meta.span()
                } else {
                    (0, 0)
                };
                lock.add_diagnostic(Diagnostic::typing(
                    self.path.clone(),
                    span,
                    TypeError::Unknown(msg),
                ));
            }
        }

        Ok(TypedExpr {
            id,
            ty: ret_ty,
            expr: typed_expr::Expr::Match(Box::new(pattern_ty), typed_arms),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
    fn infer_match_arm(
        &mut self,
        id: ExprID,
        pattern: &ParsedExpr,
        body: &ParsedExpr,
        expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        env.start_scope();
        let pattern_ty = self.infer_node(pattern, env, expected)?;
        let body_ty = self.infer_node(body, env, &None)?;
        env.end_scope();

        Ok(TypedExpr {
            id,
            ty: body_ty.ty.clone(),
            expr: typed_expr::Expr::MatchArm(Box::new(pattern_ty), Box::new(body_ty)),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    fn infer_pattern_variant(
        &mut self,
        id: ExprID,
        enum_name: &Option<Name>,
        variant_name: &Name,
        values: &[ParsedExpr],
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let resolved_name = if let Some(name) = enum_name {
            Some(name.resolved()?)
        } else {
            None
        };
        Ok(TypedExpr {
            id,
            ty: Ty::Void,
            expr: typed_expr::Expr::PatternVariant(
                resolved_name,
                variant_name.resolved()?,
                self.infer_nodes(values, env)?,
            ),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
    fn infer_member(
        &mut self,
        id: ExprID,
        receiver: &Option<Box<ParsedExpr>>,
        member_name: &str,
        expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let (typed_receiver, ret_ty) = match receiver {
            None => {
                // Unqualified: .some
                // Create a type variable that will be constrained later
                let ret = if let Some(expected) = expected {
                    expected.clone()
                } else {
                    let member_var =
                        env.new_type_variable(TypeVarKind::Member(member_name.to_string()), id);
                    Ty::TypeVar(member_var.clone())
                };

                env.constrain(Constraint::UnqualifiedMember(
                    id,
                    member_name.to_string(),
                    ret.clone(),
                ));

                (None, ret)
            }
            Some(receiver_id) => {
                // Qualified: Option.some
                let typed_receiver = self.infer_node(receiver_id, env, &None)?;

                let member_var = Ty::TypeVar(env.new_type_variable(
                    TypeVarKind::Member(member_name.to_string()),
                    typed_receiver.id,
                ));

                // Add a constraint that links the receiver type to the member
                env.constrain(Constraint::MemberAccess(
                    id,
                    typed_receiver.ty.clone(),
                    member_name.to_string(),
                    member_var.clone(),
                ));

                // Record the member access in the semantic index
                // Note: resolved_symbol will be None for now, will be filled in during constraint solving
                env.semantic_index.record_expression(
                    id,
                    ResolvedExpr::MemberAccess {
                        receiver: typed_receiver.id,
                        member_name: member_name.to_string(),
                        resolved_symbol: None,
                        ty: member_var.clone(),
                    },
                );

                // Record the span if available
                if let Some(meta) = self.meta.get(&id) {
                    let span = crate::lexing::span::Span {
                        start: meta.start.start,
                        end: meta.end.end,
                        start_line: meta.start.line,
                        start_col: meta.start.col,
                        end_line: meta.end.line,
                        end_col: meta.end.col,
                        path: self.path.clone(),
                    };
                    env.semantic_index.record_expr_span(id, span);
                }

                (Some(Box::new(typed_receiver)), member_var.clone())
            }
        };

        Ok(TypedExpr {
            id,
            ty: ret_ty,
            expr: typed_expr::Expr::Member(typed_receiver, member_name.to_string()),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
    fn infer_pattern_expr(
        &mut self,
        id: ExprID,
        parsed_expr: &ParsedExpr,
        pattern: &parsed_expr::Pattern,
        expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let Some(expected) = expected else {
            return Err(TypeError::Unknown(
                "Pattern is missing an expected type (from scrutinee).".into(),
            ));
        };

        let pattern = self.infer_pattern(id, parsed_expr, pattern, env, expected)?;

        Ok(TypedExpr {
            id,
            ty: expected.clone(),
            expr: typed_expr::Expr::ParsedPattern(pattern),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
    fn infer_pattern(
        &mut self,
        id: ExprID,
        parsed_expr: &ParsedExpr,
        pattern: &Pattern,
        env: &mut Environment,
        expected: &Ty,
    ) -> Result<typed_expr::Pattern, TypeError> {
        tracing::trace!("Inferring pattern: {pattern:?}");
        let typed_pattern = match pattern {
            Pattern::LiteralInt(val) => typed_expr::Pattern::LiteralInt(val.to_string()),
            Pattern::LiteralFloat(val) => typed_expr::Pattern::LiteralFloat(val.to_string()),
            Pattern::LiteralTrue => typed_expr::Pattern::LiteralTrue,
            Pattern::LiteralFalse => typed_expr::Pattern::LiteralFalse,
            Pattern::Bind(name) => {
                tracing::info!("inferring bind pattern: {name:?}");
                if let Name::Resolved(symbol_id, _) = name {
                    // Use the expected type for this binding
                    let scheme = Scheme::new(expected.clone(), vec![], vec![]);
                    env.declare(*symbol_id, scheme)?;
                }

                typed_expr::Pattern::Bind(name.resolved()?)
            }
            Pattern::Wildcard => typed_expr::Pattern::Wildcard,
            Pattern::Struct {
                struct_name,
                fields,
                field_names,
                rest,
            } => {
                // For struct patterns, we need to check if the expected type is a struct
                match expected {
                    Ty::Row {
                        fields: field_types,
                        row: row_variable,
                        kind: RowKind::Struct | RowKind::Record,
                        ..
                    } => {
                        let mut typed_fields = vec![];
                        let mut typed_field_names = vec![];
                        let mut matched_fields = std::collections::HashSet::new();

                        // Type check each field pattern
                        for (field_name, field_pattern_expr) in
                            field_names.iter().zip(fields.iter())
                        {
                            let field_name_str = match field_name {
                                Name::Raw(s) => s.clone(),
                                Name::Resolved(_, s) => s.clone(),
                                _ => {
                                    return Err(TypeError::Unknown(
                                        "Unsupported name type in struct pattern".to_string(),
                                    ));
                                }
                            };

                            // Find the expected type for this field
                            let field_ty = field_types
                                .iter()
                                .find(|(name, _)| name == &field_name_str)
                                .map(|(_, ty)| ty.clone())
                                .ok_or_else(|| {
                                    TypeError::Unknown(format!(
                                        "Field '{}' not found in struct",
                                        field_name_str
                                    ))
                                })?;

                            matched_fields.insert(field_name_str.clone());

                            // Type check the field pattern
                            let typed_field =
                                self.infer_node(field_pattern_expr, env, &Some(field_ty.clone()))?;
                            typed_fields.push(typed_field);
                            typed_field_names.push(field_name.resolved()?);
                        }

                        // Check if all required fields are matched (unless rest is used)
                        if !*rest && row_variable.is_none() {
                            let unmatched_fields: Vec<_> = field_types
                                .iter()
                                .filter(|(name, _)| !matched_fields.contains(name))
                                .map(|(name, _)| name.clone())
                                .collect();

                            if !unmatched_fields.is_empty() {
                                return Err(TypeError::Unknown(format!(
                                    "Missing fields in pattern: {}",
                                    unmatched_fields.join(", ")
                                )));
                            }
                        }

                        typed_expr::Pattern::Struct {
                            struct_name: struct_name.as_ref().map(|n| n.resolved()).transpose()?,
                            fields: typed_fields,
                            field_names: typed_field_names,
                            rest: *rest,
                        }
                    }
                    _ => {
                        return Err(TypeError::Unknown(format!(
                            "Cannot match struct pattern against non-struct type: {expected:?}",
                        )));
                    }
                }
            }
            Pattern::Variant {
                enum_name,
                variant_name,
                fields,
            } => {
                let resolved_name = if let Some(name) = enum_name {
                    Some(name.resolved()?)
                } else {
                    None
                };
                // The expected type should be an Enum type
                match expected {
                    Ty::Row {
                        nominal_id: Some(enum_id),
                        generics: type_args,
                        kind: RowKind::Enum,
                        ..
                    } => {
                        let Some(enum_def) = env.lookup_enum(enum_id).cloned() else {
                            return Err(TypeError::Unknown(format!(
                                "Could not resolve enum with symbol: {enum_id:?}"
                            )));
                        };
                        // Find the variant by name
                        let Some(variant) = enum_def.find_variant(variant_name) else {
                            return Err(TypeError::UnknownVariant(Name::Raw(
                                variant_name.to_string(),
                            )));
                        };
                        let values = match &variant.ty {
                            Ty::Func(params, _, _) => params,
                            Ty::Row {
                                kind: RowKind::Enum,
                                ..
                            } => {
                                // Variant with no parameters
                                &vec![]
                            }
                            _ => {
                                return Err(TypeError::Unknown(format!(
                                    "Unexpected variant type: {:?}",
                                    variant.ty
                                )));
                            }
                        };
                        // Now we have the variant definition and the concrete type arguments
                        // We need to substitute the enum's type parameters with the actual type args

                        // Create substitution map: enum type param -> concrete type arg
                        let mut substitutions = Substitutions::new();
                        for (param, arg_ty) in enum_def.type_parameters.iter().zip(type_args.iter())
                        {
                            substitutions.insert(param.type_var.clone(), arg_ty.clone());
                        }

                        // Apply substitutions to get concrete field types
                        let concrete_field_types: Vec<Ty> = values
                            .iter()
                            .map(|field_ty| {
                                ConstraintSolver::substitute_ty_with_map(field_ty, &substitutions)
                            })
                            .collect();

                        let mut typed_fields = vec![];

                        // Now match field patterns with their concrete types
                        for (field_pattern, field_ty) in
                            fields.iter().zip(concrete_field_types.iter())
                        {
                            let typed =
                                self.infer_node(field_pattern, env, &Some(field_ty.clone()))?;
                            typed_fields.push(typed);
                        }

                        typed_expr::Pattern::Variant {
                            enum_name: resolved_name,
                            variant_name: variant_name.clone(),
                            fields: typed_fields,
                        }
                    }
                    Ty::TypeVar(_) => {
                        let mut typed_fields = vec![];
                        // The expected type is still a type variable, so we can't look up variant info yet
                        // Just bind any field patterns to fresh type variables
                        for field_pattern in fields {
                            let field_ty = Ty::TypeVar(env.new_type_variable(
                                TypeVarKind::PatternBind(Name::Raw("field".into())),
                                id,
                            ));

                            typed_fields.push(self.infer_node(
                                field_pattern,
                                env,
                                &Some(field_ty),
                            )?);
                        }

                        typed_expr::Pattern::Variant {
                            enum_name: resolved_name,
                            variant_name: variant_name.clone(),
                            fields: typed_fields,
                        }
                    }
                    _ => {
                        tracing::error!(
                            "Unhandled pattern variant: {pattern:?}, expected: {expected:?}"
                        );

                        return Err(TypeError::Unknown(
                            "Could not determine pattern".to_string(),
                        ));
                    }
                }
            }
        };

        Ok(typed_pattern)
    }

    pub fn import_ty(&self, imported_symbol: &ImportedSymbol) -> Option<Ty> {
        if let Some(module) = self.module_env.get(&imported_symbol.module) {
            return module.typed_symbols.get(&imported_symbol.symbol).cloned();
        }

        None
    }

    /// Extract a Pattern from a TypedExpr that represents a pattern
    fn extract_pattern_from_typed_expr(&self, typed_expr: &TypedExpr) -> Option<Pattern> {
        match &typed_expr.expr {
            typed_expr::Expr::ParsedPattern(typed_pattern) => {
                // Convert from typed pattern to parsed pattern
                self.convert_typed_pattern_to_parsed(typed_pattern)
            }
            typed_expr::Expr::PatternVariant(enum_name, variant_name, field_exprs) => {
                // Convert from typed pattern variant to parsed pattern
                let enum_name = enum_name.as_ref().map(|rn| {
                    // ResolvedName is a tuple struct (SymbolID, String)
                    Name::Raw(rn.1.clone())
                });

                // Extract patterns from field expressions
                let mut fields = vec![];
                for field_expr in field_exprs {
                    // Field expressions should be ParsedPattern nodes
                    if let typed_expr::Expr::ParsedPattern(pattern) = &field_expr.expr
                        && let Some(converted) = self.convert_typed_pattern_to_parsed(pattern)
                    {
                        // We need to wrap the pattern back in a ParsedExpr for the Pattern::Variant fields
                        let parsed_expr = ParsedExpr {
                            id: field_expr.id,
                            expr: crate::parsed_expr::Expr::ParsedPattern(converted),
                        };
                        fields.push(parsed_expr);
                    }
                }

                Some(Pattern::Variant {
                    enum_name,
                    variant_name: variant_name.1.clone(),
                    fields,
                })
            }
            typed_expr::Expr::LiteralTrue => Some(Pattern::LiteralTrue),
            typed_expr::Expr::LiteralFalse => Some(Pattern::LiteralFalse),
            typed_expr::Expr::LiteralInt(n) => Some(Pattern::LiteralInt(n.clone())),
            typed_expr::Expr::LiteralFloat(f) => Some(Pattern::LiteralFloat(f.clone())),
            _ => None,
        }
    }

    /// Convert a typed pattern to a parsed pattern
    fn convert_typed_pattern_to_parsed(
        &self,
        typed_pattern: &typed_expr::Pattern,
    ) -> Option<Pattern> {
        match typed_pattern {
            typed_expr::Pattern::LiteralInt(n) => Some(Pattern::LiteralInt(n.clone())),
            typed_expr::Pattern::LiteralFloat(f) => Some(Pattern::LiteralFloat(f.clone())),
            typed_expr::Pattern::LiteralTrue => Some(Pattern::LiteralTrue),
            typed_expr::Pattern::LiteralFalse => Some(Pattern::LiteralFalse),
            typed_expr::Pattern::Wildcard => Some(Pattern::Wildcard),
            typed_expr::Pattern::Bind(name) => Some(Pattern::Bind(Name::Raw(name.1.clone()))),
            typed_expr::Pattern::Variant {
                enum_name,
                variant_name,
                fields,
            } => {
                let enum_name = enum_name.as_ref().map(|rn| Name::Raw(rn.1.clone()));

                // Convert typed field expressions to parsed patterns
                let mut parsed_fields = vec![];
                for field in fields {
                    // Extract the pattern from the field expression
                    if let Some(pattern) = self.extract_pattern_from_typed_expr(field) {
                        // Wrap it in a ParsedExpr
                        let parsed_expr = ParsedExpr {
                            id: field.id,
                            expr: crate::parsed_expr::Expr::ParsedPattern(pattern),
                        };
                        parsed_fields.push(parsed_expr);
                    }
                }

                Some(Pattern::Variant {
                    enum_name,
                    variant_name: variant_name.clone(),
                    fields: parsed_fields,
                })
            }
            typed_expr::Pattern::Struct {
                struct_name,
                fields,
                field_names,
                rest,
            } => {
                let struct_name = struct_name.as_ref().map(|rn| Name::Raw(rn.1.clone()));

                // Convert typed field patterns
                let mut parsed_fields = vec![];
                let mut parsed_field_names = vec![];
                for (field_name, field_expr) in field_names.iter().zip(fields.iter()) {
                    if let Some(pattern) = self.extract_pattern_from_typed_expr(field_expr) {
                        let parsed_expr = ParsedExpr {
                            id: field_expr.id,
                            expr: crate::parsed_expr::Expr::ParsedPattern(pattern),
                        };
                        parsed_fields.push(parsed_expr);
                        parsed_field_names.push(Name::Raw(field_name.1.clone()));
                    }
                }

                Some(Pattern::Struct {
                    struct_name,
                    fields: parsed_fields,
                    field_names: parsed_field_names,
                    rest: *rest,
                })
            }
        }
    }

    fn infer_record_literal(
        &mut self,
        id: ExprID,
        fields: &[ParsedExpr],
        expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let mut typed_fields = Vec::new();
        let mut field_map: HashMap<String, Ty> = HashMap::new();

        // Process fields in order, with later fields overriding earlier ones
        for field_expr in fields {
            match &field_expr.expr {
                crate::parsed_expr::Expr::Spread(spread_expr) => {
                    // Type check the spread expression
                    let typed_spread = self.infer_node(spread_expr, env, &None)?;
                    let spread_ty = typed_spread.ty.clone();

                    // Add the spread expression to typed fields
                    typed_fields.push(TypedExpr {
                        id: field_expr.id,
                        ty: spread_ty.clone(),
                        expr: typed_expr::Expr::Spread(Box::new(typed_spread)),
                    });

                    // Extract fields from the spread expression's type
                    match &spread_ty {
                        Ty::Row {
                            fields: spread_fields,
                            nominal_id: None,
                            generics: _,
                            ..
                        } => {
                            // Add all fields from the spread record
                            // These can be overridden by later fields or spreads
                            for (field_name, field_ty) in spread_fields {
                                field_map.insert(field_name.clone(), field_ty.clone());
                            }
                        }
                        Ty::TypeVar(tv) => {
                            // For type variables representing rows, we need to generate constraints
                            // This will be handled by the constraint solver
                            if matches!(tv.kind, TypeVarKind::Row) {
                                // Generate a RowConcat constraint if needed
                                // For now, we'll let the constraint solver handle this
                            }
                        }
                        _ => {
                            return Err(TypeError::Unknown(format!(
                                "Cannot spread non-record type: {spread_ty:?}"
                            )));
                        }
                    }
                }
                crate::parsed_expr::Expr::RecordField { label, value } => {
                    // Type check the field value
                    let typed_value = self.infer_node(value, env, &None)?;
                    let field_ty = typed_value.ty.clone();

                    // Create typed field
                    let typed_field = TypedExpr {
                        id: field_expr.id,
                        ty: field_ty.clone(),
                        expr: typed_expr::Expr::RecordField {
                            label: label.name_str().to_string(),
                            value: Box::new(typed_value),
                        },
                    };

                    typed_fields.push(typed_field);
                    // Later fields override earlier ones (including spread fields)
                    field_map.insert(label.name_str().to_string(), field_ty);
                }
                _ => {
                    return Err(TypeError::Unknown(
                        "Invalid expression in record literal".to_string(),
                    ));
                }
            }
        }

        // Convert HashMap back to Vec for the record type
        let field_vec: Vec<(String, Ty)> = field_map.into_iter().collect();

        // Create the record type using Row representation
        let record_ty = Ty::Row {
            fields: field_vec,
            row: None,             // No row variable for concrete record literals
            nominal_id: None,      // Records are structural types
            generics: vec![],      // Records don't have generics
            kind: RowKind::Record, // Records are structural types
        };

        // Check against expected type if provided
        if let Some(expected_ty) = expected {
            match expected_ty {
                Ty::Row {
                    fields: expected_fields,
                    row: expected_row,
                    nominal_id: None,
                    generics: _,
                    ..
                } => {
                    // Check that all expected fields are present with correct types
                    for (expected_name, expected_field_ty) in expected_fields {
                        match typed_fields.iter().find(|f| {
                            if let typed_expr::Expr::RecordField { label, .. } = &f.expr {
                                label == expected_name
                            } else {
                                false
                            }
                        }) {
                            Some(field) => {
                                if let typed_expr::Expr::RecordField { value, .. } = &field.expr
                                    && &value.ty != expected_field_ty
                                {
                                    return Err(TypeError::UnexpectedType(
                                        expected_field_ty.to_string(),
                                        value.ty.to_string(),
                                    ));
                                }
                            }
                            None => {
                                return Err(TypeError::Unknown(format!(
                                    "Missing required field '{expected_name}' in record literal"
                                )));
                            }
                        }
                    }

                    // If there's no row variable, check for extra fields
                    if expected_row.is_none() {
                        for typed_field in &typed_fields {
                            if let typed_expr::Expr::RecordField { label, .. } = &typed_field.expr
                                && !expected_fields.iter().any(|(name, _)| name == label)
                            {
                                return Err(TypeError::Unknown(format!(
                                    "Unexpected field '{label}' in record literal"
                                )));
                            }
                        }
                    }
                }
                Ty::TypeVar(_) => {
                    // Constrain the type variable to be equal to our record type
                    env.constrain(Constraint::Equality(
                        id,
                        expected_ty.clone(),
                        record_ty.clone(),
                    ));
                }
                _ => {
                    return Err(TypeError::UnexpectedType(
                        expected_ty.to_string(),
                        record_ty.to_string(),
                    ));
                }
            }
        }

        Ok(TypedExpr {
            id,
            ty: record_ty,
            expr: typed_expr::Expr::RecordLiteral(typed_fields),
        })
    }

    fn infer_record_field(
        &mut self,
        _id: ExprID,
        _label: &Name,
        _value: &ParsedExpr,
        _expected: &Option<Ty>,
        _env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        // TODO: Implement record field type checking
        Err(TypeError::Unknown(
            "Record fields are not yet implemented".to_string(),
        ))
    }

    fn infer_record_type_repr(
        &mut self,
        id: ExprID,
        fields: &[ParsedExpr],
        row_var: &Option<Box<ParsedExpr>>,
        introduces_type: bool,
        _expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let mut typed_fields = Vec::new();
        let mut field_types = Vec::new();

        // Type check each field type
        for field_expr in fields {
            match &field_expr.expr {
                crate::parsed_expr::Expr::RecordTypeField { label, ty } => {
                    // Type check the field type expression
                    let typed_ty = self.infer_node(ty, env, &None)?;

                    // Create typed field
                    let typed_field = TypedExpr {
                        id: field_expr.id,
                        ty: typed_ty.ty.clone(),
                        expr: typed_expr::Expr::RecordTypeField {
                            label: label.name_str().to_string(),
                            ty: Box::new(typed_ty.clone()),
                        },
                    };

                    typed_fields.push(typed_field);
                    field_types.push((label.name_str().to_string(), typed_ty.ty));
                }
                _ => {
                    return Err(TypeError::Unknown(
                        "Invalid expression in record type".to_string(),
                    ));
                }
            }
        }

        // Type check row variable if present
        let typed_row_var = if let Some(row_expr) = row_var {
            match &row_expr.expr {
                crate::parsed_expr::Expr::RowVariable(name) => {
                    // Create a row type variable
                    let row_type_var = env.new_type_variable(TypeVarKind::Row, row_expr.id);

                    // Generate row constraint for the row variable
                    let row_spec = RowSpec {
                        fields: field_types
                            .iter()
                            .map(|(label, ty)| {
                                (
                                    Label::from(label.clone()),
                                    FieldInfo {
                                        ty: ty.clone(),
                                        expr_id: id,
                                        metadata: Default::default(),
                                    },
                                )
                            })
                            .collect(),
                    };

                    env.constrain(Constraint::Row {
                        expr_id: id,
                        constraint: RowConstraint::HasRow {
                            type_var: row_type_var.clone(),
                            row: row_spec,
                            extension: Some(row_type_var.clone()),
                        },
                    });

                    Some(Box::new(TypedExpr {
                        id: row_expr.id,
                        ty: Ty::TypeVar(row_type_var.clone()),
                        expr: typed_expr::Expr::RowVariable(name.name_str().to_string()),
                    }))
                }
                _ => {
                    return Err(TypeError::Unknown(
                        "Invalid row variable expression".to_string(),
                    ));
                }
            }
        } else {
            None
        };

        // Create the record type using Row representation
        let record_ty = Ty::Row {
            fields: field_types,
            row: typed_row_var.as_ref().map(|tv| Box::new(tv.ty.clone())),
            nominal_id: None,      // Records are structural types
            generics: vec![],      // Records don't have generics
            kind: RowKind::Record, // Records are structural types
        };

        Ok(TypedExpr {
            id,
            ty: record_ty,
            expr: typed_expr::Expr::RecordTypeRepr {
                fields: typed_fields,
                row_var: typed_row_var,
                introduces_type,
            },
        })
    }

    fn infer_record_type_field(
        &mut self,
        id: ExprID,
        label: &Name,
        ty: &ParsedExpr,
        _expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        // Type check the field type expression
        let typed_ty = self.infer_node(ty, env, &None)?;

        Ok(TypedExpr {
            id,
            ty: typed_ty.ty.clone(),
            expr: typed_expr::Expr::RecordTypeField {
                label: label.name_str().to_string(),
                ty: Box::new(typed_ty),
            },
        })
    }

    fn infer_row_variable(
        &mut self,
        id: ExprID,
        name: &Name,
        _expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        // Create a row type variable
        let row_type_var = env.new_type_variable(TypeVarKind::Row, id);

        Ok(TypedExpr {
            id,
            ty: Ty::TypeVar(row_type_var),
            expr: typed_expr::Expr::RowVariable(name.name_str().to_string()),
        })
    }

    fn infer_spread(
        &mut self,
        id: ExprID,
        expr: &ParsedExpr,
        _expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        // Type check the expression being spread
        let typed_expr = self.infer_node(expr, env, &None)?;

        // The spread expression itself has the same type as the expression being spread
        Ok(TypedExpr {
            id,
            ty: typed_expr.ty.clone(),
            expr: typed_expr::Expr::Spread(Box::new(typed_expr)),
        })
    }
}
