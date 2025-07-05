use std::collections::HashMap;

use crate::{
    NameResolved, SourceFile, SymbolID, builtin_type, builtin_type_def,
    constraint_solver::{Constraint, Substitutions},
    environment::{Environment, RawTypeParameter, TypeParameter},
    expr::Expr,
    name::Name,
    parser::ExprID,
    ty::Ty,
    type_checker::{Scheme, TypeChecker, TypeError},
    type_defs::{
        TypeDef,
        enum_def::{EnumDef, EnumVariant, RawEnumVariant},
        protocol_def::{Conformance, ProtocolDef},
        struct_def::{
            Initializer, Method, Property, RawInitializer, RawMethod, RawProperty, StructDef,
        },
    },
    type_var_id::{TypeVarID, TypeVarKind},
};

#[derive(Debug, Clone, Default)]
pub(super) struct TypePlaceholders {
    methods: Vec<RawMethod>,
    method_requirements: Vec<RawMethod>,
    initializers: Vec<RawInitializer>,
    properties: Vec<RawProperty>,
    variants: Vec<RawEnumVariant>,
    conformances: Vec<ExprID>,
}

#[derive(Debug, PartialEq)]
pub(super) enum PredeclarationKind {
    Struct,
    Protocol,
    Enum,
    Builtin(SymbolID),
}

#[derive(Debug)]
pub(super) struct PredeclarationExprIDs {
    name: Name,
    generics: Vec<ExprID>,
    conformances: Vec<ExprID>,
    body: ExprID,
    kind: PredeclarationKind,
}

// Hoisting is responsible for grabbing stuff ahead of time so we can sorta declare stuff
// out of order. It's also responsible for figuring out what conforms to what.
impl<'a> TypeChecker<'a> {
    pub(crate) fn hoist(
        &mut self,
        items: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), TypeError> {
        let mut to_generalize = vec![];

        // The first pass goes through and finds all the named things that need to be predeclared and just defines
        // them with placeholder type variables.
        let type_defs_with_placeholders = self
            .predeclare_types(items, env, source_file)
            .map_err(|e| e.1)?;
        let lets_results = self
            .predeclare_lets(items, env, source_file)
            .map_err(|e| e.1)?;
        let func_results = self.predeclare_functions(items, env, source_file)?;

        // Then go through and actually infer stuff
        self.infer_types(type_defs_with_placeholders, env, source_file)
            .map_err(|e| e.1)?;

        to_generalize.extend(self.infer_lets(&lets_results, env, source_file)?);
        to_generalize.extend(self.infer_funcs(&func_results, env, source_file)?);

        // Solve what we can
        let substitutions = env.flush_constraints(source_file, self.symbol_table)?;

        // Update typed exprs
        env.replace_typed_exprs_values(&substitutions);

        // Generalize what we can
        for (symbol_id, _) in to_generalize {
            let scheme = &env.lookup_symbol(&symbol_id)?;
            env.declare(symbol_id, env.generalize(&scheme.ty, &symbol_id))?;
        }

        Ok(())
    }

    // We want to go through and predeclare all struct/enum/protocol names, then after that actually infer their members,
    // stashing properties, methods and initializers for each.
    #[allow(clippy::type_complexity)]
    pub(super) fn predeclare_types(
        &mut self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Vec<(SymbolID, TypePlaceholders)>, (ExprID, TypeError)> {
        let mut placeholders = vec![];

        for id in root_ids {
            let Some(expr) = source_file.get(id).cloned() else {
                log::warn!("No expr found for id: {id:?}");
                continue;
            };

            let Some(expr_ids) = self.predeclarable_type(&expr) else {
                continue;
            };

            log::debug!("Predeclaring {expr_ids:?}");

            let Name::Resolved(symbol_id, name_str) = expr_ids.name else {
                return Err((*id, TypeError::Unresolved(expr_ids.name.name_str())));
            };

            let mut raw_type_parameters = vec![];

            for id in expr_ids.generics {
                let Some(Expr::TypeRepr {
                    name: Name::Resolved(symbol_id, name_str),
                    ..
                }) = source_file.get(&id)
                else {
                    return Err((
                        id,
                        TypeError::Unresolved(
                            "did not resolve type parameter for predeclarable".into(),
                        ),
                    ));
                };

                let type_param = env.new_type_variable(
                    TypeVarKind::CanonicalTypeParameter(name_str.to_string()),
                    vec![],
                );

                env.declare(
                    *symbol_id,
                    Scheme {
                        ty: Ty::TypeVar(type_param.clone()),
                        unbound_vars: vec![type_param.clone()],
                    },
                )
                .map_err(|e| (id, e))?;

                raw_type_parameters.push(RawTypeParameter {
                    symbol_id: *symbol_id,
                    expr_id: id,
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
                PredeclarationKind::Struct => Ty::Struct(symbol_id, canonical_types.clone()),
                PredeclarationKind::Enum => Ty::Enum(symbol_id, canonical_types.clone()),
                PredeclarationKind::Protocol => Ty::Protocol(symbol_id, canonical_types.clone()),
                PredeclarationKind::Builtin(symbol_id) =>
                {
                    #[allow(clippy::expect_used)]
                    builtin_type(&symbol_id).expect("builtin type should always exist")
                }
            };

            if !matches!(expr_ids.kind, PredeclarationKind::Builtin(_)) {
                let scheme = Scheme::new(ty, unbound_vars);
                env.declare(symbol_id, scheme).map_err(|e| (*id, e))?;
            }

            let Some(Expr::Block(body_ids)) = source_file.get(&expr_ids.body).cloned() else {
                unreachable!()
            };

            let mut ty_placeholders = TypePlaceholders {
                conformances: expr_ids.conformances.clone(),
                ..Default::default()
            };

            for body_id in body_ids {
                let Some(expr) = &source_file.get(&body_id).cloned() else {
                    continue;
                };

                match &expr {
                    Expr::Property {
                        name: Name::Resolved(prop_id, name_str),
                        ..
                    } if expr_ids.kind != PredeclarationKind::Enum => {
                        let ref placeholder @ Ty::TypeVar(ref type_var) = env.placeholder(
                            &body_id,
                            format!("predecl[{name_str}]"),
                            prop_id,
                            vec![],
                        ) else {
                            unreachable!()
                        };
                        let scheme = Scheme {
                            ty: placeholder.clone(),
                            unbound_vars: vec![],
                        };
                        env.declare(*prop_id, scheme).map_err(|e| (*id, e))?;

                        ty_placeholders.properties.push(RawProperty {
                            name: name_str.clone(),
                            expr_id: body_id,
                            placeholder: type_var.clone(),
                        });
                    }
                    Expr::Init(_, func_id) if expr_ids.kind != PredeclarationKind::Enum => {
                        let Some(Expr::Func {
                            name: Some(Name::Resolved(symbol_id, name)),
                            params,
                            ..
                        }) = &source_file.get(func_id)
                        else {
                            unreachable!()
                        };

                        let ref placeholder @ Ty::TypeVar(ref type_var) = env.placeholder(
                            &body_id,
                            format!("predecl[{name}]"),
                            symbol_id,
                            vec![],
                        ) else {
                            unreachable!()
                        };
                        let scheme = Scheme {
                            ty: placeholder.clone(),
                            unbound_vars: vec![],
                        };
                        env.declare(*symbol_id, scheme).map_err(|e| (*id, e))?;

                        ty_placeholders.initializers.push(RawInitializer {
                            name: name.clone(),
                            expr_id: body_id,
                            func_id: *func_id,
                            params: params.clone(),
                            placeholder: type_var.clone(),
                        });
                    }
                    Expr::EnumVariant(name, values) => {
                        ty_placeholders.variants.push(RawEnumVariant {
                            name: name.name_str(),
                            expr_id: body_id,
                            values: values.to_vec(),
                        })
                    }
                    Expr::Func {
                        name: Some(Name::Resolved(func_id, name_str)),
                        ..
                    } => {
                        let ref placeholder @ Ty::TypeVar(ref type_var) = env.placeholder(
                            &body_id,
                            format!("predecl[{name_str}]"),
                            func_id,
                            vec![],
                        ) else {
                            unreachable!()
                        };
                        let scheme = Scheme {
                            ty: placeholder.clone(),
                            unbound_vars: vec![],
                        };
                        env.declare(*func_id, scheme).map_err(|e| (*id, e))?;

                        ty_placeholders.methods.push(RawMethod {
                            name: name_str.clone(),
                            expr_id: body_id,
                            placeholder: type_var.clone(),
                        });
                    }
                    Expr::FuncSignature {
                        name: Name::Resolved(func_id, name_str),
                        ..
                    } => {
                        let ref placeholder @ Ty::TypeVar(ref type_var) = env.placeholder(
                            &body_id,
                            format!("predecl[{name_str}]"),
                            func_id,
                            vec![],
                        ) else {
                            unreachable!()
                        };
                        let scheme = Scheme {
                            ty: placeholder.clone(),
                            unbound_vars: vec![],
                        };
                        env.declare(*func_id, scheme).map_err(|e| (*id, e))?;

                        ty_placeholders.method_requirements.push(RawMethod {
                            name: name_str.clone(),
                            expr_id: body_id,
                            placeholder: type_var.clone(),
                        });
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

            let type_params: Vec<TypeParameter> = raw_type_parameters
                .iter()
                .map(|p| TypeParameter {
                    id: p.symbol_id,
                    type_var: p.placeholder.clone(),
                })
                .collect();

            let type_def =
                env.lookup_type(&symbol_id)
                    .cloned()
                    .unwrap_or_else(|| match expr_ids.kind {
                        PredeclarationKind::Enum => TypeDef::Enum(EnumDef {
                            symbol_id,
                            name_str,
                            type_parameters: type_params,
                            variants: Default::default(),
                            methods: Default::default(),
                            conformances: Default::default(),
                        }),
                        PredeclarationKind::Struct => {
                            TypeDef::Struct(StructDef::new(symbol_id, name_str, type_params))
                        }
                        PredeclarationKind::Protocol => TypeDef::Protocol(ProtocolDef {
                            symbol_id,
                            name_str,
                            associated_types: type_params,
                            conformances: vec![],
                            properties: Default::default(),
                            methods: Default::default(),
                            initializers: Default::default(),
                            method_requirements: Default::default(),
                        }),
                        PredeclarationKind::Builtin(symbol_id) => builtin_type_def(&symbol_id),
                    });

            env.register(&type_def).map_err(|e| (*id, e))?;

            placeholders.push((type_def.symbol_id(), ty_placeholders));
        }

        Ok(placeholders)
    }

    fn infer_types(
        &mut self,
        placeholders: Vec<(SymbolID, TypePlaceholders)>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), (ExprID, TypeError)> {
        let mut substitutions: Substitutions = Default::default();

        // Sick, all the names are declared. Now let's actually infer.
        for (sym, placeholders) in &mut placeholders.into_iter() {
            let Some(mut def) = env.lookup_type(&sym).cloned() else {
                continue;
            };

            let ty = if let TypeDef::Builtin(ref def) = def {
                def.ty.clone()
            } else {
                let Ok(scheme) = env.lookup_symbol(&sym).cloned() else {
                    log::warn!("Did not find symbol for inference: {sym:?}");
                    continue;
                };

                env.instantiate(&scheme)
            };

            env.selfs.push(ty);

            if !matches!(def, TypeDef::Enum(_)) {
                let mut properties = vec![];
                for property in placeholders.properties.iter() {
                    let ty = self
                        .infer_node(&property.expr_id, env, &None, source_file)
                        .map_err(|e| (property.expr_id, e))?;
                    properties.push(Property {
                        name: property.name.clone(),
                        expr_id: property.expr_id,
                        ty: ty.clone(),
                    });

                    substitutions.insert(property.placeholder.clone(), ty.clone());
                }

                def.add_properties(properties.clone());
                env.register(&def)
                    .map_err(|e| (properties.last().map(|p| p.expr_id).unwrap_or(0), e))?;
            }

            let mut methods = vec![];
            for method in &placeholders.methods {
                let ty = self
                    .infer_node(&method.expr_id, env, &None, source_file)
                    .map_err(|e| (method.expr_id, e))?;
                methods.push(Method {
                    name: method.name.clone(),
                    expr_id: method.expr_id,
                    ty: ty.clone(),
                });
                substitutions.insert(method.placeholder.clone(), ty.clone());
            }
            def.add_methods(methods.clone());
            env.register(&def)
                .map_err(|e| (methods.last().map(|p| p.expr_id).unwrap_or(0), e))?;

            if matches!(def, TypeDef::Protocol(_)) {
                let mut method_requirements = vec![];
                for method in placeholders.method_requirements.iter() {
                    let ty = self
                        .infer_node(&method.expr_id, env, &None, source_file)
                        .map_err(|e| (method.expr_id, e))?;
                    method_requirements.push(Method {
                        name: method.name.clone(),
                        expr_id: method.expr_id,
                        ty: ty.clone(),
                    });
                    substitutions.insert(method.placeholder.clone(), ty.clone());
                }

                def.add_method_requirements(method_requirements.clone());
                env.register(&def).map_err(|e| {
                    (
                        method_requirements.last().map(|p| p.expr_id).unwrap_or(0),
                        e,
                    )
                })?;
            }

            if !matches!(def, TypeDef::Enum(_)) {
                let mut initializers = vec![];

                for initializer in placeholders.initializers.iter() {
                    let ty = self
                        .infer_node(&initializer.expr_id, env, &None, source_file)
                        .map_err(|e| (initializer.expr_id, e))?;

                    substitutions.insert(initializer.placeholder.clone(), ty.clone());

                    initializers.push(Initializer {
                        name: initializer.name.clone(),
                        expr_id: initializer.expr_id,
                        ty,
                    });
                }

                def.add_initializers(initializers.clone());
                env.register(&def)
                    .map_err(|e| (initializers.last().map(|p| p.expr_id).unwrap_or(0), e))?;
            }

            if matches!(def, TypeDef::Enum(_)) {
                let mut variants = vec![];
                for variant in placeholders.variants.iter() {
                    let ty = self
                        .infer_node(
                            &variant.expr_id,
                            env,
                            &Some(Ty::Enum(def.symbol_id(), vec![])),
                            source_file,
                        )
                        .map_err(|e| (variant.expr_id, e))?;
                    variants.push(EnumVariant {
                        name: variant.name.clone(),
                        ty,
                    });
                }

                def.add_variants(variants);
                env.register(&def).map_err(|e| (0, e))?;
            }

            let mut conformance_constraints = vec![];
            let mut conformances = vec![];
            for id in placeholders.conformances.iter() {
                let ty = self
                    .infer_node(id, env, &None, source_file)
                    .map_err(|e| (*id, e))?;
                let Ty::Protocol(symbol_id, associated_types) = ty else {
                    log::error!("Didn't get protocol for expr id: {id} {ty:?}",);
                    continue;
                };

                let conformance = Conformance::new(symbol_id, associated_types);
                conformances.push(conformance.clone());
                conformance_constraints.push(Constraint::ConformsTo {
                    expr_id: *id,
                    type_def: def.symbol_id(),
                    conformance,
                });
            }

            def.add_conformances(conformances);
            env.register(&def).map_err(|e| (0, e))?;

            for constraint in conformance_constraints {
                env.constrain(constraint);
            }

            env.selfs.pop();
        }

        env.replace_constraint_values(&substitutions);
        env.replace_typed_exprs_values(&substitutions);

        Ok(())
    }

    fn predeclare_functions(
        &mut self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Vec<(ExprID, SymbolID, TypeVarID)>, TypeError> {
        log::trace!("Predeclaring funcs");

        let mut func_ids = vec![];

        // Predeclaration pass, just declare placeholders
        for id in root_ids.iter() {
            let Some(Expr::Func {
                name: Some(Name::Resolved(symbol_id, name_str)),
                ..
            }) = source_file.get(id).cloned()
            else {
                continue;
            };

            let ref placeholder @ Ty::TypeVar(ref type_var) =
                env.placeholder(id, format!("predecl[{name_str}]"), &symbol_id, vec![])
            else {
                unreachable!()
            };

            // Stash this func ID so we can fully infer it in the next loop
            func_ids.push((*id, symbol_id, type_var.clone()));

            env.declare(
                symbol_id,
                Scheme {
                    ty: placeholder.clone(),
                    unbound_vars: vec![],
                },
            )?;
        }

        Ok(func_ids)
    }

    fn infer_funcs(
        &mut self,
        func_ids: &[(ExprID, SymbolID, TypeVarID)],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Vec<(SymbolID, Ty)>, TypeError> {
        let mut placeholder_substitutions = HashMap::new();
        let mut results = vec![];

        for (expr_id, symbol_id, placeholder) in func_ids {
            let ty = self.infer_node(
                expr_id,
                env,
                &Some(Ty::TypeVar(placeholder.clone())),
                source_file,
            )?;
            env.declare(
                *symbol_id,
                Scheme {
                    ty: ty.clone(),
                    unbound_vars: vec![],
                },
            )?;

            placeholder_substitutions.insert(placeholder.clone(), ty.clone());
            results.push((*symbol_id, ty))
        }

        env.replace_typed_exprs_values(&placeholder_substitutions);
        env.replace_constraint_values(&placeholder_substitutions);

        Ok(results)
    }

    #[allow(clippy::type_complexity)]
    fn predeclare_lets(
        &mut self,
        items: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Vec<(ExprID, SymbolID, TypeVarID)>, (ExprID, TypeError)> {
        log::trace!("Predeclaring lets");
        let mut result = vec![];

        for id in items {
            let Some(Expr::Assignment(lhs, _)) = source_file.get(id).cloned() else {
                continue;
            };

            let Some(Expr::Let(Name::Resolved(symbol_id, name_str), _)) = source_file.get(&lhs)
            else {
                continue;
            };

            let ref placeholder @ Ty::TypeVar(ref type_var) =
                env.placeholder(id, format!("predecl[{name_str}]"), symbol_id, vec![])
            else {
                unreachable!()
            };

            let scheme = Scheme {
                ty: placeholder.clone(),
                unbound_vars: vec![],
            };
            env.declare(*symbol_id, scheme).map_err(|e| (*id, e))?;
            result.push((*id, *symbol_id, type_var.clone()));
        }

        Ok(result)
    }

    fn infer_lets(
        &mut self,
        let_ids: &[(ExprID, SymbolID, TypeVarID)],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<Vec<(SymbolID, Ty)>, TypeError> {
        log::trace!("infer lets");

        let mut placeholder_substitutions = HashMap::new();
        let mut results = vec![];

        for (id, symbol, type_var) in let_ids {
            let ty = self.infer_node(id, env, &None, source_file)?;
            placeholder_substitutions.insert(type_var.clone(), ty.clone());
            results.push((*symbol, ty.clone()));
            env.declare(
                *symbol,
                Scheme {
                    ty,
                    unbound_vars: vec![],
                },
            )?;
        }

        env.replace_constraint_values(&placeholder_substitutions);

        Ok(results)
    }

    fn predeclarable_type(&self, expr: &Expr) -> Option<PredeclarationExprIDs> {
        if let Expr::Struct {
            name,
            generics,
            conformances,
            body,
        }
        | Expr::Extend {
            name,
            generics,
            conformances,
            body,
        } = expr.clone()
        {
            if let Name::Resolved(sym, _) = name
                && builtin_type(&sym).is_some()
            {
                return Some(PredeclarationExprIDs {
                    name,
                    generics,
                    conformances,
                    body,
                    kind: PredeclarationKind::Builtin(sym),
                });
            } else {
                return Some(PredeclarationExprIDs {
                    name,
                    generics,
                    conformances,
                    body,
                    kind: PredeclarationKind::Struct,
                });
            }
        }

        if let Expr::ProtocolDecl {
            name,
            associated_types: generics,
            body,
            conformances,
        } = expr.clone()
        {
            return Some(PredeclarationExprIDs {
                name,
                generics,
                conformances,
                body,
                kind: PredeclarationKind::Protocol,
            });
        }

        if let Expr::EnumDecl {
            name,
            generics,
            conformances,
            body,
        } = expr.clone()
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
