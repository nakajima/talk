use crate::{
    NameResolved, SourceFile,
    constraint_solver::Substitutions,
    environment::{
        EnumDef, EnumVariant, Environment, Initializer, Method, Property, ProtocolDef,
        RawEnumVariant, RawInitializer, RawMethod, RawProperty, StructDef, TypeDef,
    },
    expr::Expr,
    name::Name,
    parser::ExprID,
    ty::Ty,
    type_checker::{Scheme, TypeChecker, TypeError, TypeVarKind},
};

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
    // We want to go through and predeclare all struct/enum/protocol names, then after that actually infer their members,
    // stashing properties, methods and initializers for each.
    //
    // Note: we may need to break this up into multiple methods to handle multiple files..
    pub(super) fn predeclare_types(
        &mut self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), (ExprID, TypeError)> {
        let mut type_defs = vec![];
        let mut type_def_conformances = vec![];
        let mut method_placeholders = vec![];
        let mut property_placeholders = vec![];
        let mut initializer_placeholders = vec![];

        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();
            let Some(expr_ids) = self.predeclarable_type(&expr) else {
                continue;
            };

            let Name::Resolved(symbol_id, name_str) = expr_ids.name else {
                return Err((*id, TypeError::Unresolved(expr_ids.name.name_str())));
            };

            let mut methods: Vec<RawMethod> = Default::default();
            let mut properties: Vec<RawProperty> = Default::default();
            let mut type_parameters = vec![];
            let mut initializers = vec![];
            let mut variants = vec![];

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

                let type_param = env.new_type_variable(TypeVarKind::CanonicalTypeParameter(
                    format!("{}{}", name_str, symbol_id.0),
                ));

                env.declare(
                    *symbol_id,
                    Scheme {
                        ty: Ty::TypeVar(type_param.clone()),
                        unbound_vars: vec![],
                    },
                );

                type_parameters.push(Ty::TypeVar(type_param));
            }

            type_def_conformances.push((symbol_id, expr_ids.conformances));

            // The type, using the canonical placeholders.
            let ty = match expr_ids.kind {
                PredeclarationKind::Struct => Ty::Struct(symbol_id, type_parameters.clone()),
                PredeclarationKind::Enum => Ty::Enum(symbol_id, type_parameters.clone()),
                PredeclarationKind::Protocol => Ty::Protocol(symbol_id, type_parameters.clone()),
            };

            // The unbound vars of this type ARE its canonical placeholders.
            let unbound_vars = type_parameters
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

            let mut ty_initializers = vec![];
            let mut ty_methods = vec![];
            let mut ty_properties = vec![];

            for body_id in body_ids {
                let expr = &source_file.get(&body_id).cloned().unwrap();
                match &expr {
                    Expr::Property {
                        name: Name::Resolved(prop_id, name_str),
                        ..
                    } if expr_ids.kind != PredeclarationKind::Enum => {
                        let placeholder = env.placeholder(&body_id, name_str.clone(), &prop_id);
                        let scheme = Scheme {
                            ty: placeholder.clone(),
                            unbound_vars: vec![],
                        };
                        env.declare(*prop_id, scheme);

                        ty_properties.push(placeholder);

                        properties.push(RawProperty {
                            name: name_str.clone(),
                            expr_id: body_id,
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

                        let placeholder = env.placeholder(&body_id, name.clone(), &symbol_id);
                        let scheme = Scheme {
                            ty: placeholder.clone(),
                            unbound_vars: vec![],
                        };
                        env.declare(*symbol_id, scheme);

                        ty_initializers.push(placeholder);
                        initializers.push(RawInitializer {
                            name: name.clone(),
                            expr_id: body_id,
                            func_id: *func_id,
                            params: params.clone(),
                        });
                    }
                    Expr::EnumVariant(name, values) => variants.push(RawEnumVariant {
                        name: name.name_str(),
                        expr_id: body_id,
                        values: values.to_vec(),
                    }),
                    Expr::Func {
                        name: Some(Name::Resolved(func_id, name_str)),
                        ..
                    } => {
                        let placeholder = env.placeholder(&body_id, name_str.clone(), &func_id);
                        let scheme = Scheme {
                            ty: placeholder.clone(),
                            unbound_vars: vec![],
                        };
                        env.declare(*func_id, scheme);

                        ty_methods.push(placeholder);

                        methods.push(RawMethod {
                            name: name_str.clone(),
                            expr_id: body_id,
                        });
                    }
                    Expr::FuncSignature {
                        name: Name::Resolved(func_id, name_str),
                        ..
                    } => {
                        let placeholder = env.placeholder(&body_id, name_str.clone(), &func_id);
                        let scheme = Scheme {
                            ty: placeholder.clone(),
                            unbound_vars: vec![],
                        };
                        env.declare(*func_id, scheme);

                        ty_methods.push(placeholder);

                        methods.push(RawMethod {
                            name: name_str.clone(),
                            expr_id: body_id,
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
                    type_parameters,
                    raw_variants: variants,
                    variants: Default::default(),
                    raw_methods: methods,
                    methods: Default::default(),
                    conformances: Default::default(),
                }),
                PredeclarationKind::Struct => TypeDef::Struct(StructDef::new(
                    symbol_id,
                    name_str,
                    type_parameters,
                    properties,
                    methods,
                    initializers,
                )),
                PredeclarationKind::Protocol => TypeDef::Protocol(ProtocolDef {
                    symbol_id,
                    name_str,
                    associated_types: type_parameters,
                    conformances: vec![],
                    raw_properties: properties,
                    properties: Default::default(),
                    raw_methods: methods,
                    methods: Default::default(),
                    raw_initializers: initializers,
                    initializers: Default::default(),
                }),
            };

            type_defs.push(type_def.clone());

            method_placeholders.push(ty_methods);
            property_placeholders.push(ty_properties);
            initializer_placeholders.push(ty_initializers);

            // Register updated definition
            match type_def {
                TypeDef::Enum(def) => env.register_enum(def),
                TypeDef::Struct(def) => env.register_struct(def),
                TypeDef::Protocol(def) => env.register_protocol(def),
            }
        }

        let mut substitutions: Substitutions = Default::default();

        // Sick, all the names are declared. Now let's actually infer.
        for (i, mut def) in &mut type_defs.into_iter().enumerate() {
            let mut initializers = vec![];
            let mut properties = vec![];
            let mut methods = vec![];
            let mut variants = vec![];

            if !matches!(def, TypeDef::Enum(_)) {
                for (j, initializer) in def.raw_initializers().iter().enumerate() {
                    let ty = self
                        .infer_node(
                            &initializer.expr_id,
                            env,
                            &Some(Ty::Struct(def.symbol_id(), def.type_parameters().clone())),
                            source_file,
                        )
                        .map_err(|e| (initializer.expr_id, e))?;

                    let Ty::TypeVar(placeholder) = &initializer_placeholders[i][j] else {
                        unreachable!();
                    };
                    substitutions.insert(placeholder.clone(), ty.clone());

                    initializers.push(Initializer {
                        name: initializer.name.clone(),
                        expr_id: initializer.expr_id,
                        ty: ty,
                    });
                }
            }

            if !matches!(def, TypeDef::Enum(_)) {
                for (j, property) in def.raw_properties().iter().enumerate() {
                    let ty = self
                        .infer_node(&property.expr_id, env, &None, source_file)
                        .map_err(|e| (property.expr_id, e))?;
                    properties.push(Property {
                        name: property.name.clone(),
                        expr_id: property.expr_id,
                        ty: ty.clone(),
                    });

                    let Ty::TypeVar(placeholder) = &property_placeholders[i][j] else {
                        unreachable!();
                    };
                    substitutions.insert(placeholder.clone(), ty.clone());
                }
            }

            for (j, method) in def.raw_methods().iter().enumerate() {
                let ty = self
                    .infer_node(&method.expr_id, env, &None, source_file)
                    .map_err(|e| (method.expr_id, e))?;
                methods.push(Method {
                    name: method.name.clone(),
                    expr_id: method.expr_id,
                    ty: ty.clone(),
                });
                // env.constrain_equality(method.expr_id, method_placeholders[i][j].clone(), ty);
                let Ty::TypeVar(placeholder) = &method_placeholders[i][j] else {
                    unreachable!();
                };
                substitutions.insert(placeholder.clone(), ty.clone());
            }

            if matches!(def, TypeDef::Enum(_)) {
                for variant in def.raw_variants().iter() {
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
            }

            def.set_initializers(initializers);
            def.set_properties(properties);
            def.set_methods(methods);
            def.set_variants(variants);

            // Register the inferred struct

            // Register updated definition
            match def {
                TypeDef::Enum(def) => env.register_enum(def),
                TypeDef::Struct(def) => env.register_struct(def),
                TypeDef::Protocol(def) => env.register_protocol(def),
            }
        }

        env.replace_constraint_values(&substitutions);

        // Track conformances.
        for (type_id, conformance_ids) in type_def_conformances {
            let mut conformances = vec![];
            for id in conformance_ids.iter() {
                let Some(Ty::Protocol(symbol_id, _)) =
                    env.typed_exprs.get(id).map(|t| t.ty.clone()).clone()
                else {
                    log::error!(
                        "Didn't get protocol for expr id: {id}: {:?}",
                        env.typed_exprs.get(id)
                    );
                    continue;
                };

                conformances.push(symbol_id);
            }

            let Some(type_def) = &mut env.lookup_type_mut(&type_id) else {
                log::error!("Did not get type def for symbol: {type_id:?}");
                continue;
            };

            println!("setting {type_def:?} conformances: {conformances:?}");

            match type_def {
                TypeDef::Enum(def) => def.conformances = conformances,
                TypeDef::Struct(def) => def.conformances = conformances,
                TypeDef::Protocol(def) => def.conformances = conformances,
            }
        }

        Ok(())
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
