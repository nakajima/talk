use std::collections::HashMap;

use crate::{
    NameResolved, SourceFile, SymbolID,
    constraint_solver::{Constraint, Substitutions},
    environment::{
        EnumDef, EnumVariant, Environment, Initializer, Method, Property, ProtocolDef,
        RawEnumVariant, RawInitializer, RawMethod, RawProperty, StructDef, TypeDef,
    },
    expr::Expr,
    name::Name,
    parser::ExprID,
    ty::Ty,
    type_checker::{Scheme, TypeChecker, TypeError},
    type_var_id::{TypeVarID, TypeVarKind},
};

#[derive(Debug, Clone, Default)]
pub(super) struct TypePlaceholders {
    methods: Vec<RawMethod>,
    method_requirements: Vec<RawMethod>,
    initializers: Vec<RawInitializer>,
    properties: Vec<RawProperty>,
    variants: Vec<RawEnumVariant>,
}

#[derive(PartialEq)]
pub(super) enum PredeclarationKind {
    Struct,
    Protocol,
    Enum,
}

pub(super) struct PredeclarationExprIDs {
    name: Name,
    generics: Vec<ExprID>,
    conformances: Vec<ExprID>,
    body: ExprID,
    kind: PredeclarationKind,
}

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
        let (type_defs_with_placeholders, type_conformances) = self
            .predeclare_types(items, env, source_file)
            .map_err(|e| e.1)?;
        let lets_results = self.predeclare_lets(items, env, source_file);
        let func_results = self.predeclare_functions(items, env, source_file)?;

        // Then go through and actually infer stuff
        self.infer_types(
            type_defs_with_placeholders,
            type_conformances,
            env,
            source_file,
        )
        .map_err(|e| e.1)?;

        to_generalize.extend(self.infer_lets(&lets_results, env, source_file)?);
        to_generalize.extend(self.infer_funcs(&func_results, env, source_file)?);

        // Solve what we can
        let substitutions = env.flush_constraints(source_file, self.symbol_table)?;

        // Update typed exprs
        env.replace_typed_exprs_values(&substitutions);

        // Generalize what we can
        for (symbol_id, _) in to_generalize {
            let ty = &env.lookup_symbol(&symbol_id).unwrap().ty;
            env.declare(symbol_id, env.generalize(ty, &symbol_id));
        }

        Ok(())
    }

    // We want to go through and predeclare all struct/enum/protocol names, then after that actually infer their members,
    // stashing properties, methods and initializers for each.
    pub(super) fn predeclare_types(
        &mut self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<
        (
            Vec<(SymbolID, TypePlaceholders)>,
            Vec<(SymbolID, Vec<ExprID>)>,
        ),
        (ExprID, TypeError),
    > {
        let mut type_def_conformances = vec![];
        let mut placeholders = vec![];

        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();
            let Some(expr_ids) = self.predeclarable_type(&expr) else {
                continue;
            };

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
                    TypeVarKind::CanonicalTypeParameter(format!("{}{}", name_str, symbol_id.0)),
                    vec![],
                );

                env.declare(
                    *symbol_id,
                    Scheme {
                        ty: Ty::TypeVar(type_param.clone()),
                        unbound_vars: vec![],
                    },
                );

                raw_type_parameters.push(Ty::TypeVar(type_param));
            }

            type_def_conformances.push((symbol_id, expr_ids.conformances));

            // The type, using the canonical placeholders.
            let ty = match expr_ids.kind {
                PredeclarationKind::Struct => Ty::Struct(symbol_id, raw_type_parameters.clone()),
                PredeclarationKind::Enum => Ty::Enum(symbol_id, raw_type_parameters.clone()),
                PredeclarationKind::Protocol => {
                    Ty::Protocol(symbol_id, raw_type_parameters.clone())
                }
            };

            // The unbound vars of this type ARE its canonical placeholders.
            let unbound_vars = raw_type_parameters
                .iter()
                .filter_map(|ty| match ty {
                    Ty::TypeVar(tv) => Some(tv.clone()),
                    _ => None,
                })
                .collect();

            let scheme = Scheme::new(ty, unbound_vars);
            env.declare(symbol_id, scheme);

            let Some(Expr::Block(body_ids)) = source_file.get(&expr_ids.body).cloned() else {
                unreachable!()
            };

            let mut ty_placeholders = TypePlaceholders::default();

            for body_id in body_ids {
                let expr = &source_file.get(&body_id).cloned().unwrap();
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
                        env.declare(*prop_id, scheme);

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
                        env.declare(*symbol_id, scheme);

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
                        env.declare(*func_id, scheme);

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
                        env.declare(*func_id, scheme);

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

            let type_def = match expr_ids.kind {
                PredeclarationKind::Enum => TypeDef::Enum(EnumDef {
                    name: Some(symbol_id),
                    name_str,
                    type_parameters: raw_type_parameters,
                    variants: Default::default(),
                    methods: Default::default(),
                    conformances: Default::default(),
                }),
                PredeclarationKind::Struct => {
                    TypeDef::Struct(StructDef::new(symbol_id, name_str, raw_type_parameters))
                }
                PredeclarationKind::Protocol => TypeDef::Protocol(ProtocolDef {
                    symbol_id,
                    name_str,
                    associated_types: raw_type_parameters,
                    conformances: vec![],
                    properties: Default::default(),
                    methods: Default::default(),
                    initializers: Default::default(),
                    method_requirements: Default::default(),
                }),
            };

            env.register(&type_def);

            placeholders.push((type_def.symbol_id(), ty_placeholders));
        }

        Ok((placeholders, type_def_conformances))
    }

    fn infer_types(
        &mut self,
        placeholders: Vec<(SymbolID, TypePlaceholders)>,
        type_def_conformances: Vec<(SymbolID, Vec<ExprID>)>,
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), (ExprID, TypeError)> {
        let mut substitutions: Substitutions = Default::default();

        // Sick, all the names are declared. Now let's actually infer.
        for (sym, placeholders) in &mut placeholders.into_iter() {
            let mut def = env.lookup_type(&sym).unwrap().clone();

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

                def.set_properties(properties);
                env.register(&def);
            }

            let mut methods = vec![];
            for method in &placeholders.methods {
                let ty = self
                    .infer_node(&method.expr_id, env, &None, source_file)
                    .map_err(|e| (method.expr_id, e))
                    .unwrap();
                methods.push(Method {
                    name: method.name.clone(),
                    expr_id: method.expr_id,
                    ty: ty.clone(),
                });
                substitutions.insert(method.placeholder.clone(), ty.clone());
            }
            def.set_methods(methods);
            env.register(&def);

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

                def.set_method_requirements(method_requirements);
                env.register(&def);
            }

            if !matches!(def, TypeDef::Enum(_)) {
                let mut initializers = vec![];

                for initializer in placeholders.initializers.iter() {
                    let ty = self
                        .infer_node(
                            &initializer.expr_id,
                            env,
                            &Some(Ty::Struct(def.symbol_id(), def.type_parameters().clone())),
                            source_file,
                        )
                        .map_err(|e| (initializer.expr_id, e))?;

                    substitutions.insert(initializer.placeholder.clone(), ty.clone());

                    initializers.push(Initializer {
                        name: initializer.name.clone(),
                        expr_id: initializer.expr_id,
                        ty,
                    });
                }

                def.set_initializers(initializers);
                env.register(&def);
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

                def.set_variants(variants);
                env.register(&def);
            }
        }

        env.replace_constraint_values(&substitutions);

        let mut conformance_constraints = vec![];

        // Track conformances.
        for (type_id, conformance_ids) in type_def_conformances {
            let mut conformances = vec![];
            for id in conformance_ids.iter() {
                let Ty::Protocol(symbol_id, _) = self
                    .infer_node(id, env, &None, source_file)
                    .map_err(|e| (*id, e))?
                else {
                    log::error!("Didn't get protocol for expr id: {id}");
                    continue;
                };

                conformance_constraints.push(Constraint::ConformsTo {
                    expr_id: *id,
                    type_def: type_id,
                    protocol: symbol_id,
                });

                conformances.push(symbol_id);
            }

            let Some(def) = env.lookup_type_mut(&type_id) else {
                log::error!("Did not get type def for symbol: {type_id:?}");
                continue;
            };

            def.set_conformances(conformances);
        }

        env.constraints.extend(conformance_constraints);

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
            let Expr::Func {
                name: Some(Name::Resolved(symbol_id, name_str)),
                ..
            } = source_file.get(id).unwrap().clone()
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
            );
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
            );

            placeholder_substitutions.insert(placeholder.clone(), ty.clone());
            results.push((*symbol_id, ty))
        }

        env.replace_typed_exprs_values(&placeholder_substitutions);
        env.replace_constraint_values(&placeholder_substitutions);

        Ok(results)
    }

    fn predeclare_lets(
        &mut self,
        items: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Vec<(ExprID, SymbolID, TypeVarID)> {
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
            env.declare(*symbol_id, scheme);
            result.push((*id, *symbol_id, type_var.clone()));
        }

        result
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
            );
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
        } = expr.clone()
        {
            return Some(PredeclarationExprIDs {
                name,
                generics,
                conformances,
                body,
                kind: PredeclarationKind::Struct,
            });
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
