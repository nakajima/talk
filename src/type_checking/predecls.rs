use crate::{
    NameResolved, SourceFile,
    constraint_solver::Substitutions,
    environment::{
        Environment, Initializer, Method, Property, RawInitializer, RawMethod, RawProperty,
        StructDef,
    },
    expr::Expr,
    name::Name,
    parser::ExprID,
    ty::Ty,
    type_checker::{Scheme, TypeChecker, TypeError, TypeVarKind},
};

impl<'a> TypeChecker<'a> {
    // We want to go through and predeclare all struct names, then after that actually infer their members,
    // stashing properties, methods and initializers for each.
    pub(super) fn predeclare_structs(
        &mut self,
        root_ids: &[ExprID],
        env: &mut Environment,
        source_file: &mut SourceFile<NameResolved>,
    ) -> Result<(), (ExprID, TypeError)> {
        let mut struct_defs = vec![];
        let mut method_placeholders = vec![];
        let mut property_placeholders = vec![];
        let mut initializer_placeholders = vec![];

        for id in root_ids {
            let expr = source_file.get(id).unwrap().clone();
            let Expr::Struct(name, generics, body) = expr else {
                continue;
            };

            let Name::Resolved(symbol_id, name_str) = name else {
                return Err((*id, TypeError::Unresolved(name.name_str())));
            };

            let mut methods: Vec<RawMethod> = Default::default();
            let mut properties: Vec<RawProperty> = Default::default();
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

            let mut struct_initializers = vec![];
            let mut struct_methods = vec![];
            let mut struct_properties = vec![];
            for body_id in body_ids {
                let expr = &source_file.get(&body_id).cloned().unwrap();
                match &expr {
                    Expr::Property {
                        name: Name::Resolved(prop_id, name_str),
                        ..
                    } => {
                        let placeholder = env.placeholder(&body_id, name_str.clone(), &prop_id);
                        let scheme = Scheme {
                            ty: placeholder.clone(),
                            unbound_vars: vec![],
                        };
                        env.declare(*prop_id, scheme);

                        struct_properties.push(placeholder);

                        properties.push(RawProperty {
                            name: name_str.clone(),
                            expr_id: body_id,
                        });
                    }
                    Expr::Init(_, func_id) => {
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

                        struct_initializers.push(placeholder);
                        initializers.push(RawInitializer {
                            name: name.clone(),
                            expr_id: body_id,
                            func_id: *func_id,
                            params: params.clone(),
                        });
                    }
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

                        struct_methods.push(placeholder);

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

            let struct_def = StructDef::new(
                symbol_id,
                name_str,
                type_parameters.clone(),
                properties,
                methods,
                initializers,
            );

            struct_defs.push(struct_def.clone());

            method_placeholders.push(struct_methods);
            property_placeholders.push(struct_properties);
            initializer_placeholders.push(struct_initializers);

            // Register updated definition
            env.register_struct(struct_def);
        }

        let mut substitutions: Substitutions = Default::default();

        // Sick, all the names are declared. Now let's actually infer.
        for (i, mut struct_def) in &mut struct_defs.into_iter().enumerate() {
            let mut initializers = vec![];
            let mut properties = vec![];
            let mut methods = vec![];
            for (j, initializer) in struct_def.raw_initializers.iter().enumerate() {
                let ty = self
                    .infer_node(
                        &initializer.expr_id,
                        env,
                        &Some(Ty::Struct(
                            struct_def.symbol_id,
                            struct_def.type_parameters.clone(),
                        )),
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

            for (j, property) in struct_def.raw_properties.iter().enumerate() {
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

            for (j, method) in struct_def.raw_methods.iter().enumerate() {
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

            struct_def.initializers = initializers;
            struct_def.properties = properties;
            struct_def.methods = methods;

            // Register the inferred struct
            env.register_struct(struct_def.clone());
        }

        env.replace_constraint_values(substitutions);

        Ok(())
    }
}
