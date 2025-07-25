use tracing::info_span;

use crate::{
    SymbolID, builtin_type,
    conformance::Conformance,
    constraint::Constraint,
    environment::{Environment, RawTypeParameter, TypeParameter, free_type_vars},
    name::Name,
    parsed_expr::ParsedExpr,
    parsing::expr_id::ExprID,
    substitutions::Substitutions,
    ty::Ty,
    type_checker::{Scheme, TypeChecker, TypeError},
    type_def::{EnumVariant, Initializer, Method, Property, TypeDef, TypeDefKind},
    type_var_id::{TypeVarID, TypeVarKind},
    typed_expr::Expr,
};

#[derive(Default, Debug)]
pub(super) struct TypePlaceholders<'a> {
    methods: Vec<RawMethod<'a>>,
    method_requirements: Vec<RawMethod<'a>>,
    initializers: Vec<RawInitializer<'a>>,
    properties: Vec<RawProperty<'a>>,
    variants: Vec<RawEnumVariant<'a>>,
    conformances: Vec<ParsedExpr>,
}

#[derive(Debug, PartialEq)]
pub(super) enum PredeclarationKind {
    Struct,
    Protocol,
    Enum,
    Builtin(SymbolID),
}

#[derive(Debug)]
pub(super) struct PredeclarationExprIDs<'a> {
    name: &'a Name,
    generics: &'a Vec<ParsedExpr>,
    conformances: &'a Vec<ParsedExpr>,
    body: &'a ParsedExpr,
    kind: PredeclarationKind,
}

// Hoisting is responsible for grabbing stuff ahead of time so we can sorta declare stuff
// out of order. It's also responsible for figuring out what conforms to what.
impl<'a> TypeChecker<'a> {
    pub(crate) fn hoist(
        &mut self,
        items: &'a [ParsedExpr],
        env: &mut Environment,
    ) -> Result<(), TypeError> {
        tracing::info!("importing types");
        for module in self.module_env.values() {
            // This should probably all live in TypeDef or something..
            for (type_symbol, type_def) in module.types.iter() {
                if type_symbol.0 <= 0 {
                    continue; // Don't re-import builtins
                }

                let Some(our_symbol) = self.symbol_table.find_imported(type_symbol) else {
                    tracing::warn!("Unable to find imported symbol for {type_def:?}");
                    continue;
                };

                let mut our_type_def = type_def.clone();
                our_type_def.symbol_id = *our_symbol;

                let mut our_type_parameters = vec![];
                let mut substitutions = Substitutions::new();
                for t in type_def.type_parameters().iter() {
                    let new_type_var =
                        env.new_type_variable(t.type_var.kind.clone(), t.type_var.expr_id);

                    substitutions.insert(t.type_var.clone(), Ty::TypeVar(new_type_var.clone()));

                    our_type_parameters.push(TypeParameter {
                        id: *self.symbol_table.find_imported(type_symbol).ok_or(
                            TypeError::Unknown(format!(
                                "Unable to find imported symbol for type parameter: {t:?}"
                            )),
                        )?,
                        type_var: new_type_var,
                    })
                }

                our_type_def.type_parameters = our_type_parameters;

                for member in our_type_def.members.values_mut() {
                    for type_var in free_type_vars(member.ty()) {
                        substitutions.insert(
                            type_var.clone(),
                            Ty::TypeVar(
                                env.new_type_variable(type_var.kind.clone(), type_var.expr_id),
                            ),
                        )
                    }

                    member.replace(&substitutions)
                }

                tracing::debug!(
                    "Importing type: {our_type_def:?}, substitutions: {substitutions:?}"
                );

                env.register(&our_type_def)?;
            }
        }

        let _s = info_span!("hoisting", path = self.path.to_str()).entered();
        let mut to_generalize = vec![];

        // The first pass goes through and finds all the named things that need to be predeclared and just defines
        // them with placeholder type variables.
        let type_defs_with_placeholders = Self::predeclare_types(items, env).map_err(|e| e.1)?;
        let lets_results = self.predeclare_lets(items, env).map_err(|e| e.1)?;
        let func_results = self.predeclare_functions(items, env)?;

        // Then go through and actually infer stuff
        self.infer_types(type_defs_with_placeholders, env)
            .map_err(|e| e.1)?;

        to_generalize.extend(self.infer_lets(&lets_results, env)?);
        to_generalize.extend(self.infer_funcs(&func_results, env)?);

        // Solve what we can
        let mut solution = env.flush_constraints(self.meta)?;
        env.replace_typed_exprs_values(&mut solution.substitutions);

        // Generalize what we can
        for (symbol_id, _) in to_generalize {
            let scheme = env.lookup_symbol(&symbol_id)?.clone();
            let scheme = env.generalize(&scheme.ty(), &symbol_id);
            env.declare(symbol_id, scheme)?;
        }

        Ok(())
    }

    // We want to go through and predeclare all struct/enum/protocol names, then after that actually infer their members,
    // stashing properties, methods and initializers for each.

    #[allow(clippy::type_complexity)]
    pub(super) fn predeclare_types(
        roots: &'a [ParsedExpr],
        env: &mut Environment,
    ) -> Result<Vec<(SymbolID, TypePlaceholders<'a>)>, (ExprID, TypeError)> {
        let mut placeholders = vec![];

        for root in roots {
            let Some(expr_ids) = Self::predeclarable_type(root) else {
                continue;
            };

            tracing::debug!("Predeclaring {expr_ids:?}");

            let Name::Resolved(symbol_id, name_str) = expr_ids.name else {
                return Err((root.id, TypeError::Unresolved(expr_ids.name.name_str())));
            };

            let mut raw_type_parameters = vec![];

            for generic in expr_ids.generics {
                let crate::parsed_expr::Expr::TypeRepr {
                    name: Name::Resolved(symbol_id, name_str),
                    ..
                } = &generic.expr
                else {
                    return Err((
                        generic.id,
                        TypeError::Unresolved(
                            "did not resolve type parameter for predeclarable".into(),
                        ),
                    ));
                };

                let type_param = env.new_type_variable(
                    TypeVarKind::CanonicalTypeParameter(name_str.to_string()),
                    generic.id,
                );

                env.declare(
                    *symbol_id,
                    Scheme::new(
                        Ty::TypeVar(type_param.clone()),
                        vec![type_param.clone()],
                        vec![],
                    ),
                )
                .map_err(|e| (generic.id, e))?;

                raw_type_parameters.push(RawTypeParameter {
                    symbol_id: *symbol_id,
                    expr_id: generic.id,
                    placeholder: type_param,
                });
            }

            let unbound_vars: Vec<TypeVarID> = raw_type_parameters
                .iter()
                .map(|t| t.placeholder.clone())
                .collect();
            let canonical_types: Vec<Ty> = unbound_vars
                .iter()
                .map(|t| Ty::TypeVar(t.clone()))
                .collect();

            // The type, using the canonical placeholders.
            let ty = match expr_ids.kind {
                PredeclarationKind::Struct => Ty::Struct(*symbol_id, canonical_types.clone()),
                PredeclarationKind::Enum => Ty::Enum(*symbol_id, canonical_types.clone()),
                PredeclarationKind::Protocol => Ty::Protocol(*symbol_id, canonical_types.clone()),
                PredeclarationKind::Builtin(symbol_id) =>
                {
                    #[allow(clippy::expect_used)]
                    builtin_type(&symbol_id).expect("builtin type should always exist")
                }
            };

            if !matches!(expr_ids.kind, PredeclarationKind::Builtin(_)) {
                let scheme = Scheme::new(ty, unbound_vars, vec![]);
                env.declare(*symbol_id, scheme).map_err(|e| (root.id, e))?;
            }

            let crate::parsed_expr::Expr::Block(ref body_exprs) = expr_ids.body.expr else {
                unreachable!()
            };

            let mut ty_placeholders = TypePlaceholders {
                conformances: expr_ids.conformances.to_vec(),
                ..Default::default()
            };

            let mut last_variant_index = 0;
            let mut last_property_index = 0;

            for body_expr in body_exprs {
                match &body_expr.expr {
                    crate::parsed_expr::Expr::Property {
                        name: Name::Resolved(prop_id, name_str),
                        default_value,
                        ..
                    } if expr_ids.kind != PredeclarationKind::Enum => {
                        let ref placeholder @ Ty::TypeVar(ref type_var) = env.placeholder(
                            &body_expr.id,
                            format!("predecl[{name_str}]"),
                            prop_id,
                            vec![],
                        ) else {
                            unreachable!()
                        };
                        let scheme = Scheme::new(placeholder.clone(), vec![], vec![]);
                        env.declare(*prop_id, scheme)
                            .map_err(|e| (body_expr.id, e))?;

                        ty_placeholders.properties.push(RawProperty {
                            index: last_property_index,
                            name: name_str.clone(),
                            expr: body_expr,
                            placeholder: type_var.clone(),
                            default_value,
                        });

                        last_property_index += 1;
                    }
                    crate::parsed_expr::Expr::Init(_, func_expr)
                        if expr_ids.kind != PredeclarationKind::Enum =>
                    {
                        let crate::parsed_expr::Expr::Func {
                            name: Some(Name::Resolved(symbol_id, name)),
                            params,
                            ..
                        } = &func_expr.expr
                        else {
                            unreachable!("didn't get resolved init: {:?}", func_expr.expr)
                        };

                        let ref placeholder @ Ty::TypeVar(ref type_var) = env.placeholder(
                            &func_expr.id,
                            format!("predecl[{name}]"),
                            symbol_id,
                            vec![],
                        ) else {
                            unreachable!()
                        };
                        let scheme = Scheme::new(placeholder.clone(), vec![], vec![]);
                        env.declare(*symbol_id, scheme)
                            .map_err(|e| (func_expr.id, e))?;

                        ty_placeholders.initializers.push(RawInitializer {
                            name: name.clone(),
                            expr: body_expr,
                            func_id: func_expr.id,
                            params,
                            placeholder: type_var.clone(),
                        });
                    }
                    crate::parsed_expr::Expr::EnumVariant(name, values) => {
                        ty_placeholders.variants.push(RawEnumVariant {
                            tag: last_variant_index,
                            name: name.name_str(),
                            expr: body_expr,
                            values,
                        });

                        last_variant_index += 1;
                    }
                    crate::parsed_expr::Expr::Func {
                        name: Some(Name::Resolved(func_id, name_str)),
                        ..
                    } => {
                        let ref placeholder @ Ty::TypeVar(ref type_var) = env.placeholder(
                            &body_expr.id,
                            format!("predecl[{name_str}]"),
                            func_id,
                            vec![],
                        ) else {
                            unreachable!()
                        };
                        let scheme = Scheme::new(placeholder.clone(), vec![], vec![]);
                        env.declare(*func_id, scheme)
                            .map_err(|e| (body_expr.id, e))?;

                        ty_placeholders.methods.push(RawMethod {
                            name: name_str.clone(),
                            expr: body_expr,
                            placeholder: type_var.clone(),
                        });
                    }
                    crate::parsed_expr::Expr::FuncSignature {
                        name: Name::Resolved(func_id, name_str),
                        ..
                    } => {
                        let ref placeholder @ Ty::TypeVar(ref type_var) = env.placeholder(
                            &body_expr.id,
                            format!("predecl[{name_str}]"),
                            func_id,
                            vec![],
                        ) else {
                            unreachable!()
                        };
                        let scheme = Scheme::new(placeholder.clone(), vec![], vec![]);
                        env.declare(*func_id, scheme)
                            .map_err(|e| (body_expr.id, e))?;

                        ty_placeholders.method_requirements.push(RawMethod {
                            name: name_str.clone(),
                            expr: body_expr,
                            placeholder: type_var.clone(),
                        });
                    }
                    _ => {
                        return {
                            tracing::error!("Unhandled property: {:?}", body_expr.expr);
                            Err((
                                body_expr.id,
                                TypeError::Unknown(format!(
                                    "Unhandled property: {:?}",
                                    body_expr.expr
                                )),
                            ))
                        };
                    }
                }
            }

            let type_params: Vec<TypeParameter> = raw_type_parameters
                .iter()
                .map(|p| TypeParameter {
                    id: p.symbol_id,
                    type_var: p.placeholder.clone(),
                })
                .collect();

            let type_def = env.lookup_type(symbol_id).cloned().unwrap_or_else(|| {
                let kind = match expr_ids.kind {
                    PredeclarationKind::Enum => TypeDefKind::Enum,
                    PredeclarationKind::Struct => TypeDefKind::Struct,
                    PredeclarationKind::Protocol => TypeDefKind::Protocol,
                    PredeclarationKind::Builtin(symbol_id) =>
                    {
                        #[allow(clippy::unwrap_used)]
                        TypeDefKind::Builtin(builtin_type(&symbol_id).unwrap())
                    }
                };

                TypeDef {
                    symbol_id: *symbol_id,
                    name_str: name_str.clone(),
                    kind,
                    type_parameters: type_params,
                    members: Default::default(),
                    conformances: Default::default(),
                    row_var: None,  // Row vars can be added later if needed
                }
            });

            env.register(&type_def).map_err(|e| (root.id, e))?;

            placeholders.push((type_def.symbol_id(), ty_placeholders));
        }

        Ok(placeholders)
    }

    fn infer_types(
        &mut self,
        placeholders: Vec<(SymbolID, TypePlaceholders)>,
        env: &mut Environment,
    ) -> Result<(), (ExprID, TypeError)> {
        let mut substitutions: Substitutions = Default::default();

        // Sick, all the names are declared. Now let's actually infer.
        for (sym, placeholders) in &mut placeholders.into_iter() {
            let Some(mut def) = env.lookup_type(&sym).cloned() else {
                continue;
            };

            // TODO: Should this be happening in typedef ty instead of here?
            let ty = if let TypeDefKind::Builtin(ref ty) = def.kind {
                ty.clone()
            } else {
                let Ok(scheme) = env.lookup_symbol(&sym).cloned() else {
                    tracing::warn!("Did not find symbol for inference: {sym:?}");
                    continue;
                };

                env.instantiate(&scheme)
            };

            env.selfs.push(ty);

            if def.kind != TypeDefKind::Enum {
                let mut properties = vec![];
                for property in placeholders.properties.iter() {
                    let typed_expr = self
                        .infer_node(property.expr, env, &None)
                        .map_err(|e| (property.expr.id, e))?;
                    properties.push(Property {
                        index: property.index,
                        name: property.name.clone(),
                        expr_id: property.expr.id,
                        ty: typed_expr.ty.clone(),
                        has_default: matches!(
                            typed_expr.expr,
                            Expr::Property {
                                default_value: Some(_),
                                ..
                            }
                        ),
                    });

                    substitutions.insert(property.placeholder.clone(), typed_expr.ty.clone());
                }

                def.add_properties(properties.clone());
                env.register(&def)
                    .map_err(|e| (properties.last().map(|p| p.expr_id).unwrap_or_default(), e))?;
            }

            let mut methods = vec![];
            for method in &placeholders.methods {
                let typed_expr = self
                    .infer_method(method.expr.id, method.expr, env)
                    .map_err(|e| (method.expr.id, e))?;
                methods.push(Method {
                    name: method.name.clone(),
                    expr_id: method.expr.id,
                    ty: typed_expr.ty.clone(),
                });

                substitutions.insert(method.placeholder.clone(), typed_expr.ty.clone());
            }
            def.add_methods(methods.clone());
            env.register(&def)
                .map_err(|e| (methods.last().map(|p| p.expr_id).unwrap_or_default(), e))?;

            if def.kind == TypeDefKind::Protocol {
                let mut method_requirements = vec![];
                for method in placeholders.method_requirements.iter() {
                    let typed_expr = self
                        .infer_node(method.expr, env, &None)
                        .map_err(|e| (method.expr.id, e))?;
                    method_requirements.push(Method {
                        name: method.name.clone(),
                        expr_id: method.expr.id,
                        ty: typed_expr.ty.clone(),
                    });
                    substitutions.insert(method.placeholder.clone(), typed_expr.ty.clone());
                }

                def.add_method_requirements(method_requirements.clone());
                env.register(&def).map_err(|e| {
                    (
                        method_requirements
                            .last()
                            .map(|p| p.expr_id)
                            .unwrap_or_default(),
                        e,
                    )
                })?;
            }

            if def.kind != TypeDefKind::Enum {
                let mut initializers = vec![];

                for initializer in placeholders.initializers.iter() {
                    let typed_expr = self
                        .infer_node(initializer.expr, env, &None)
                        .map_err(|e| (initializer.expr.id, e))?;

                    substitutions.insert(initializer.placeholder.clone(), typed_expr.ty.clone());

                    initializers.push(Initializer {
                        name: initializer.name.clone(),
                        expr_id: initializer.expr.id,
                        ty: typed_expr.ty.clone(),
                    });
                }

                def.add_initializers(initializers.clone());
                env.register(&def).map_err(|e| {
                    (
                        initializers.last().map(|p| p.expr_id).unwrap_or_default(),
                        e,
                    )
                })?;
            }

            if def.kind == TypeDefKind::Enum {
                let mut variants = vec![];
                for variant in placeholders.variants.iter() {
                    let typed_expr = self
                        .infer_node(variant.expr, env, &Some(Ty::Enum(def.symbol_id(), vec![])))
                        .map_err(|e| (variant.expr.id, e))?;
                    variants.push(EnumVariant {
                        tag: variant.tag,
                        name: variant.name.clone(),
                        ty: typed_expr.ty.clone(),
                    });
                }

                def.add_variants(variants);
                env.register(&def).map_err(|e| (Default::default(), e))?;
            }

            let mut conformance_constraints = vec![];
            let mut conformances = vec![];
            for conformance_expr in placeholders.conformances.iter() {
                let typed_expr = self
                    .infer_node(conformance_expr, env, &None)
                    .map_err(|e| (conformance_expr.id, e))?;

                let Ty::Protocol(name, associated_types) = &typed_expr.ty else {
                    tracing::error!("Didn't get protocol for expr: {typed_expr:?}",);
                    continue;
                };

                let conformance = Conformance::new(*name, associated_types.to_vec());
                conformances.push(conformance.clone());
                conformance_constraints.push(Constraint::ConformsTo {
                    expr_id: conformance_expr.id,
                    ty: def.ty(),
                    conformance,
                });
            }

            def.add_conformances(conformances);
            env.register(&def).map_err(|e| (Default::default(), e))?;

            for constraint in conformance_constraints {
                env.constrain(constraint);
            }

            env.selfs.pop();
        }

        env.replace_constraint_values(&mut substitutions);
        env.replace_typed_exprs_values(&mut substitutions);

        Ok(())
    }

    fn predeclare_functions(
        &mut self,
        roots: &'a [ParsedExpr],
        env: &mut Environment,
    ) -> Result<Vec<(&'a ParsedExpr, &'a SymbolID, TypeVarID)>, TypeError> {
        tracing::trace!("Predeclaring funcs");

        let mut func_ids = vec![];

        // Predeclaration pass, just declare placeholders
        for func_expr in roots.iter() {
            let crate::parsed_expr::Expr::Func {
                name: Some(Name::Resolved(symbol_id, name_str)),
                ..
            } = &func_expr.expr
            else {
                continue;
            };

            let ref placeholder @ Ty::TypeVar(ref type_var) = env.placeholder(
                &func_expr.id,
                format!("predecl[{name_str}]"),
                symbol_id,
                vec![],
            ) else {
                unreachable!()
            };

            // Stash this func ID so we can fully infer it in the next loop
            func_ids.push((func_expr, symbol_id, type_var.clone()));

            env.declare(*symbol_id, Scheme::new(placeholder.clone(), vec![], vec![]))?;
        }

        Ok(func_ids)
    }

    fn infer_funcs(
        &mut self,
        func_ids: &[(&'a ParsedExpr, &'a SymbolID, TypeVarID)],
        env: &mut Environment,
    ) -> Result<Vec<(SymbolID, Ty)>, TypeError> {
        let mut placeholder_substitutions = Substitutions::new();
        let mut results = vec![];

        for (func_expr, symbol_id, placeholder) in func_ids {
            let typed_expr =
                self.infer_node(func_expr, env, &Some(Ty::TypeVar(placeholder.clone())))?;
            env.declare(
                **symbol_id,
                Scheme::new(typed_expr.ty.clone(), vec![], vec![]),
            )?;

            placeholder_substitutions.insert(placeholder.clone(), typed_expr.ty.clone());
            results.push((**symbol_id, typed_expr.ty.clone()))
        }

        env.replace_typed_exprs_values(&mut placeholder_substitutions);
        env.replace_constraint_values(&mut placeholder_substitutions);

        Ok(results)
    }

    #[allow(clippy::type_complexity)]
    fn predeclare_lets(
        &mut self,
        items: &'a [ParsedExpr],
        env: &mut Environment,
    ) -> Result<Vec<(&'a ParsedExpr, &'a SymbolID, TypeVarID)>, (ExprID, TypeError)> {
        tracing::trace!("Predeclaring lets");
        let mut result = vec![];

        for parsed_expr in items {
            let crate::parsed_expr::Expr::Assignment(lhs, _) = &parsed_expr.expr else {
                continue;
            };

            let crate::parsed_expr::Expr::Let(Name::Resolved(symbol_id, name_str), _) = &lhs.expr
            else {
                continue;
            };

            let ref placeholder @ Ty::TypeVar(ref type_var) =
                env.placeholder(&lhs.id, format!("predecl[{name_str}]"), symbol_id, vec![])
            else {
                unreachable!()
            };

            let scheme = Scheme::new(placeholder.clone(), vec![], vec![]);
            env.declare(*symbol_id, scheme).map_err(|e| (lhs.id, e))?;
            result.push((&**lhs, symbol_id, type_var.clone()));
        }

        Ok(result)
    }

    fn infer_lets(
        &mut self,
        let_ids: &[(&'a ParsedExpr, &'a SymbolID, TypeVarID)],
        env: &mut Environment,
    ) -> Result<Vec<(SymbolID, Ty)>, TypeError> {
        tracing::trace!("infer lets");

        let mut placeholder_substitutions = Substitutions::new();
        let mut results = vec![];

        for (id, symbol, type_var) in let_ids {
            let typed_expr = self.infer_node(id, env, &None)?;
            placeholder_substitutions.insert(type_var.clone(), typed_expr.ty.clone());
            results.push((**symbol, typed_expr.ty.clone()));
            env.declare(**symbol, Scheme::new(typed_expr.ty.clone(), vec![], vec![]))?;
        }

        env.replace_constraint_values(&mut placeholder_substitutions);

        Ok(results)
    }

    fn predeclarable_type(parsed_expr: &ParsedExpr) -> Option<PredeclarationExprIDs<'_>> {
        let expr = &parsed_expr.expr;

        if let crate::parsed_expr::Expr::Struct {
            name,
            generics,
            conformances,
            body,
        }
        | crate::parsed_expr::Expr::Extend {
            name,
            generics,
            conformances,
            body,
        } = expr
        {
            let kind = if let Name::Resolved(sym, _) = name
                && builtin_type(sym).is_some()
            {
                PredeclarationKind::Builtin(*sym)
            } else {
                PredeclarationKind::Struct
            };

            return Some(PredeclarationExprIDs {
                name,
                generics,
                conformances,
                body,
                kind,
            });
        }

        if let crate::parsed_expr::Expr::ProtocolDecl {
            name,
            associated_types: generics,
            body,
            conformances,
        } = expr
        {
            return Some(PredeclarationExprIDs {
                name,
                generics,
                conformances,
                body,
                kind: PredeclarationKind::Protocol,
            });
        }

        if let crate::parsed_expr::Expr::EnumDecl {
            name,
            generics,
            conformances,
            body,
        } = expr
        {
            return Some(PredeclarationExprIDs {
                name,
                generics,
                conformances,
                body,
                kind: PredeclarationKind::Enum,
            });
        }

        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawInitializer<'a> {
    pub name: String,
    pub expr: &'a ParsedExpr,
    pub func_id: ExprID,
    pub params: &'a [ParsedExpr],
    pub placeholder: TypeVarID,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawMethod<'a> {
    pub name: String,
    pub expr: &'a ParsedExpr,
    pub placeholder: TypeVarID,
}

impl<'a> RawMethod<'a> {
    pub fn new(name: String, expr: &'a ParsedExpr, placeholder: TypeVarID) -> Self {
        Self {
            name,
            expr,
            placeholder,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawProperty<'a> {
    pub index: usize,
    pub name: String,
    pub expr: &'a ParsedExpr,
    pub placeholder: TypeVarID,
    pub default_value: &'a Option<Box<ParsedExpr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawEnumVariant<'a> {
    pub tag: usize,
    pub name: String,
    pub expr: &'a ParsedExpr,
    pub values: &'a [ParsedExpr],
}
