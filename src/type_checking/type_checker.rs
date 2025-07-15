use std::{collections::HashMap, path::PathBuf};

use tracing::trace_span;

use crate::{
    NameResolved, SymbolID, SymbolTable, Typed,
    compiling::compilation_session::SharedCompilationSession,
    conformance_checker::ConformanceError,
    constraint::Constraint,
    constraint_solver::ConstraintSolver,
    diagnostic::Diagnostic,
    name::{Name, ResolvedName},
    name_resolver::NameResolverError,
    parsed_expr::{self, IncompleteExpr, ParsedExpr, Pattern},
    parser::ExprID,
    source_file::SourceFile,
    substitutions::Substitutions,
    synthesis::synthesize_inits,
    token_kind::TokenKind,
    ty::Ty,
    type_defs::{TypeDef, protocol_def::Conformance},
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
    type_map: HashMap<ExprID, TypedExpr>,
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
    ) -> Self {
        Self {
            session,
            symbol_table,
            path,
            type_map: Default::default(),
        }
    }

    pub fn infer(
        &mut self,
        source_file: &'a SourceFile<NameResolved>,
        env: &mut Environment,
    ) -> SourceFile<Typed> {
        self.infer_without_prelude(env, source_file)
    }

    pub fn infer_without_prelude(
        &mut self,
        env: &mut Environment,
        source_file: &'a SourceFile<NameResolved>,
    ) -> SourceFile<Typed> {
        let roots = source_file.roots();
        // synthesize_inits(&mut source_file, self.symbol_table, env);

        // Just define names for all of the funcs, structs and enums
        if let Err(e) = self.hoist(roots, env)
            && let Ok(mut lock) = self.session.lock()
        {
            lock.add_diagnostic(Diagnostic::typing(
                source_file.path.clone(),
                roots.first().map(|r| r.id).unwrap_or_default(),
                e,
            ));
        }

        let mut typed_roots = vec![];
        for parsed_expr in roots {
            #[allow(clippy::unwrap_used)]
            match self.infer_node(parsed_expr, env, &None) {
                Ok(typed_expr) => typed_roots.push(typed_expr),
                Err(e) => {
                    if let Ok(mut lock) = self.session.lock() {
                        lock.add_diagnostic(Diagnostic::typing(
                            source_file.path.clone(),
                            parsed_expr.id,
                            e,
                        ))
                    }
                }
            }
        }

        source_file.to_typed(
            typed_roots,
            self.type_map.clone(),
            source_file.phase_data.scope_tree.clone(),
        )
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
        let _s = trace_span!("infer_node", expr = format!("{parsed_expr:?}")).entered();

        let mut ty = match &parsed_expr.expr {
            crate::parsed_expr::Expr::Incomplete(expr_id) => self.handle_incomplete(expr_id),
            crate::parsed_expr::Expr::LiteralTrue => {
                checked_expected(expected, Ty::Bool);
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: Ty::Bool,
                    expr: typed_expr::Expr::LiteralTrue,
                })
            }
            crate::parsed_expr::Expr::LiteralFalse => {
                checked_expected(expected, Ty::Bool);
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: Ty::Bool,
                    expr: typed_expr::Expr::LiteralFalse,
                })
            }
            crate::parsed_expr::Expr::Loop(cond, body) => {
                self.infer_loop(parsed_expr.id, cond, body, env)
            }
            crate::parsed_expr::Expr::If(condition, consequence, alternative) => {
                let ty = self.infer_if(parsed_expr.id, condition, consequence, alternative, env);
                if let Ok(ty) = &ty {
                    checked_expected(expected, ty.ty.clone())?;
                }

                ty
            }
            crate::parsed_expr::Expr::Call {
                callee,
                type_args,
                args,
            } => self.infer_call(parsed_expr.id, env, callee, type_args, args, expected),
            crate::parsed_expr::Expr::LiteralInt(v) => {
                checked_expected(expected, Ty::Int);
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: Ty::Bool,
                    expr: typed_expr::Expr::LiteralInt(v.to_string()),
                })
            }
            crate::parsed_expr::Expr::LiteralFloat(v) => {
                checked_expected(expected, Ty::Float);
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: Ty::Bool,
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
            crate::parsed_expr::Expr::CallArg { value, label } => {
                let label = if let Some(name) = label {
                    Some(name.resolved()?)
                } else {
                    None
                };

                let typed = self.infer_node(value, env, expected)?;
                Ok(TypedExpr {
                    id: parsed_expr.id,
                    ty: typed.ty.clone(),
                    expr: typed_expr::Expr::CallArg {
                        label,
                        value: Box::new(typed),
                    },
                })
            }
            crate::parsed_expr::Expr::Init(Some(struct_id), func_id) => {
                self.infer_init(parsed_expr.id, struct_id, func_id, expected, env)
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
            _ => Err(TypeError::Unknown(format!(
                "Don't know how to type check {parsed_expr:?}"
            ))),
        };

        match &ty {
            Ok(ty) => {
                self.type_map.insert(parsed_expr.id, ty.clone());
            }
            Err(e) => {
                tracing::error!("error inferring {parsed_expr:?}: {e:?}");
                if let Ok(mut lock) = self.session.lock() {
                    lock.add_diagnostic(Diagnostic::typing(
                        self.path.clone(),
                        parsed_expr.id,
                        e.clone(),
                    ));
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
        body: &Box<ParsedExpr>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let mut inferred_associated_types: Vec<TypedExpr> = vec![];
        for generic in associated_types {
            inferred_associated_types.push(self.infer_node(generic, env, &None)?);
        }

        let Name::Resolved(symbol_id, name_str) = name else {
            return Err(TypeError::Unresolved(name.name_str()));
        };

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::ProtocolDecl {
                name: ResolvedName(*symbol_id, name_str.to_string()),
                associated_types: inferred_associated_types.clone(),
                body: self.infer_node(body, env, &None)?.into(),
                conformances: self.infer_nodes(conformances, env)?,
            },
            ty: Ty::Protocol(
                *symbol_id,
                inferred_associated_types
                    .iter()
                    .map(|t| t.ty.clone())
                    .collect(),
            ),
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
            .map(|expr| self.infer_node(&expr, env, &None))
            .transpose()?;
        let default_value = default_value
            .as_ref()
            .map(|expr| self.infer_node(&expr, env, &None))
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
        body: &Box<ParsedExpr>,
        conformances: &[ParsedExpr],
        generics: &[ParsedExpr],
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let scheme = env.lookup_symbol(enum_id)?;
        let ty = scheme.ty.clone();

        Ok(TypedExpr {
            id,
            ty: ty.clone(),
            expr: typed_expr::Expr::EnumDecl {
                name: ResolvedName(*enum_id, name),
                conformances: self.infer_nodes(conformances, env)?,
                generics: self.infer_nodes(generics, env)?,
                body: self.infer_node(body, env, &Some(ty))?.into(),
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
        let Some(Ty::Enum(enum_id, _)) = expected else {
            unreachable!("should always be called with expected = Enum, got: {expected:?}",);
        };
        let values = self.infer_nodes(values, env)?;
        let ty = Ty::EnumVariant(*enum_id, values.iter().map(|v| v.ty.clone()).collect());

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::EnumVariant(ResolvedName(*enum_id, name.name_str()), values),
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
            Ty::TypeVar(env.new_type_variable(TypeVarKind::FuncParam(name.name_str())))
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

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected,))]
    fn infer_init(
        &mut self,
        id: ExprID,
        struct_id: &SymbolID,
        func_id: &Box<ParsedExpr>,
        expected: &Option<Ty>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let inferred = self.infer_node(func_id, env, expected)?;
        let params = match inferred.ty.clone() {
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

        Ok(TypedExpr {
            id,
            expr: crate::typed_expr::Expr::Init(*struct_id, inferred.into()),
            ty: Ty::Init(*struct_id, params.clone()),
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
        body: &Box<ParsedExpr>,
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

        let ty = Ty::Struct(
            *symbol_id,
            inferred_generics.iter().map(|t| t.ty.clone()).collect(),
        );

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Extend {
                name: ResolvedName(*symbol_id, name_str.to_string()),
                generics: inferred_generics,
                conformances: self.infer_nodes(conformances, env)?,
                body: Box::new(self.infer_node(body, env, &None)?),
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
        body: &Box<ParsedExpr>,
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

        let ty = Ty::Struct(
            *symbol_id,
            inferred_generics.iter().map(|t| t.ty.clone()).collect(),
        );

        Ok(TypedExpr {
            id,
            expr: typed_expr::Expr::Struct {
                name: ResolvedName(*symbol_id, name_str.to_string()),
                generics: inferred_generics,
                conformances: self.infer_nodes(conformances, env)?,
                body: Box::new(self.infer_node(body, env, &None)?),
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
            .unwrap_or_else(|| Ty::TypeVar(env.new_type_variable(TypeVarKind::Element)));

        Ok(TypedExpr {
            id,
            ty: Ty::Struct(SymbolID::ARRAY, vec![ty]),
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
        body: &Box<ParsedExpr>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let cond = if let Some(cond) = cond {
            Some(Box::new(self.infer_node(&cond, env, &Some(Ty::Bool))?))
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
        condition: &Box<ParsedExpr>,
        consequence: &Box<ParsedExpr>,
        alternative: &Option<Box<ParsedExpr>>,
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let condition = self.infer_node(condition, env, &Some(Ty::Bool))?;
        let consequence = self.infer_node(consequence, env, &None)?;
        let alt = if let Some(alternative) = alternative {
            let alternative = self.infer_node(alternative, env, &None)?;
            env.constrain(Constraint::Equality(
                alternative.id,
                consequence.ty.clone(),
                alternative.ty.clone(),
            ));
            Some(consequence.clone())
        } else {
            // TODO
            // consequence.optional()
            None
        };

        Ok(TypedExpr {
            id,
            ty: consequence.ty.clone(),
            expr: typed_expr::Expr::If(
                Box::new(condition),
                Box::new(consequence),
                alt.map(Box::new),
            ),
        })
    }

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected,))]
    #[allow(clippy::too_many_arguments)]
    fn infer_call(
        &mut self,
        id: ExprID,
        env: &mut Environment,
        callee: &Box<ParsedExpr>,
        type_args: &[ParsedExpr],
        args: &[ParsedExpr],
        expected: &Option<Ty>,
    ) -> Result<TypedExpr, TypeError> {
        let mut ret_var = if let Some(expected) = expected {
            expected.clone()
        } else {
            // Avoid borrow checker issue by creating the type variable before any borrows
            let call_return_var = env.new_type_variable(TypeVarKind::CallReturn);
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
            typed_expr::Expr::Variable(ResolvedName(symbol_id, name_str))
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
                    Ty::Struct(*symbol_id, type_args.clone()),
                    struct_def.canonical_type_vars(),
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
        lhs: &Box<ParsedExpr>,
        rhs: &Box<ParsedExpr>,
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
                Some(
                    Ty::Struct(symbol_id, _) | Ty::Enum(symbol_id, _) | Ty::Protocol(symbol_id, _),
                ) => (*symbol_id, "Self".to_string()),
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
                let Ty::Protocol(protocol_id, associated_types) = typed_conformance.ty.clone()
                else {
                    return Err(TypeError::Unknown(format!(
                        "{typed_conformance:?} is not a protocol",
                    )));
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
                    conformance: Conformance::new(protocol_id.clone(), associated_types.to_vec()),
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
                Ty::TypeVar(env.new_type_variable(TypeVarKind::SelfVar(symbol_id)))
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
        ret: &Box<ParsedExpr>,
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

    #[tracing::instrument(level = "DEBUG", skip(self, env))]
    #[allow(clippy::too_many_arguments)]
    fn infer_func(
        &mut self,
        id: ExprID,
        name: &Option<Name>,
        generics: &[ParsedExpr],
        params: &[ParsedExpr],
        captures: &[SymbolID],
        body: &Box<ParsedExpr>,
        ret: &Option<Box<ParsedExpr>>,
        env: &mut Environment,
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

        let mut ret_ty =
            self.infer_node(body, env, &annotated_ret_ty.as_ref().map(|t| t.ty.clone()))?;

        if let Some(annotated_ret_ty) = &annotated_ret_ty
            && let Some(ret_id) = ret
        {
            env.constrain(Constraint::Equality(
                ret_id.id,
                ret_ty.ty.clone(),
                annotated_ret_ty.ty.clone(),
            ));

            ret_ty = annotated_ret_ty.clone();
        }

        env.end_scope();

        let func_ty = Ty::Func(
            param_vars.iter().map(|p| p.ty.clone()).collect(),
            Box::new(ret_ty.ty.clone()),
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
            let new_scheme = if let Ok(existing_scheme) = env.lookup_symbol_mut(symbol_id) {
                tracing::trace!("merging schemes: {existing_scheme:?}.ty = {inferred_ty:?}");
                existing_scheme.ty = inferred_ty.clone();
                existing_scheme.clone()
            } else {
                Scheme::new(inferred_ty.clone(), vec![], vec![])
            };

            // Declare a monomorphized scheme. It'll be generalized by the hoisting pass.
            env.declare(*symbol_id, new_scheme)?;
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
            (None, Ty::TypeVar(env.new_type_variable(TypeVarKind::Let)))
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
            Name::_Self(_sym) => {
                if let Some(self_) = env.selfs.last() {
                    if let Ty::Protocol(symbol_id, _) = self_ {
                        Ty::TypeVar(env.new_type_variable(TypeVarKind::SelfVar(*symbol_id)))
                    } else {
                        self_.clone()
                    }
                } else {
                    return Err(TypeError::Unknown("No value found for `self`".into()));
                }
            }
            Name::Resolved(symbol_id, _) => {
                let scheme = env.lookup_symbol(symbol_id)?.clone();

                // If the symbol refers to a generic type parameter that is already represented
                // by a canonical / placeholder type-variable, we should NOT create a fresh
                // instantiation every time it is referenced inside the same scope. Doing so
                // would break the expected equality between occurrences (e.g. the return type
                // of `fizz<T>` must be the same `T` that appears in its parameter list).
                // Instead, we use the scheme's own type directly.

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
        rhs: &Box<ParsedExpr>,
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
        lhs_id: &Box<ParsedExpr>,
        rhs_id: &Box<ParsedExpr>,
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
                    Ty::TypeVar(env.new_type_variable(TypeVarKind::BinaryOperand(op.clone())))
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

    #[tracing::instrument(level = "DEBUG", skip(self, env, expected))]
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
            let typed_item = self.infer_node(item, env, expected)?;
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
            } else {
                block_return_ty = Some(ty);
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
        pattern: &Box<ParsedExpr>,
        arms: &[ParsedExpr],
        env: &mut Environment,
    ) -> Result<TypedExpr, TypeError> {
        let pattern_ty = self.infer_node(pattern, env, &None)?;
        let mut typed_arms = vec![];
        let mut arm_tys = vec![];

        for arm in arms {
            let typed = self.infer_node(arm, env, &Some(pattern_ty.ty.clone()))?;
            let ty = typed.ty.clone();
            arm_tys.push(ty);
            typed_arms.push(typed);
        }

        let ret_ty = arm_tys.first().map(|t| t.clone()).unwrap_or(Ty::Void);

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
        pattern: &Box<ParsedExpr>,
        body: &Box<ParsedExpr>,
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
                        env.new_type_variable(TypeVarKind::Member(member_name.to_string()));
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

                let member_var = Ty::TypeVar(
                    env.new_type_variable(TypeVarKind::Member(member_name.to_string())),
                );

                // Add a constraint that links the receiver type to the member
                env.constrain(Constraint::MemberAccess(
                    id,
                    typed_receiver.ty.clone(),
                    member_name.to_string(),
                    member_var.clone(),
                ));

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
                    Ty::Enum(enum_id, type_args) => {
                        let Some(enum_def) = env.lookup_enum(&enum_id).cloned() else {
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
                    Ty::EnumVariant(_enum_id, values_types) => {
                        let mut typed_fields = vec![];

                        // Now match field patterns with their concrete types
                        for (field_pattern, field_ty) in fields.iter().zip(values_types.iter()) {
                            typed_fields.push(self.infer_node(
                                field_pattern,
                                env,
                                &Some(field_ty.clone()),
                            )?)
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
}
