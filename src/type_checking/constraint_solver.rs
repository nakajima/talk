use crate::{
    SymbolID, SymbolTable,
    conformance_checker::{ConformanceChecker, ConformanceError},
    constraint::Constraint,
    environment::{Environment, TypeParameter},
    expr::Expr,
    name::Name,
    parser::ExprID,
    substitutions::Substitutions,
    ty::Ty,
    type_checker::{Scheme, TypeError},
    type_defs::TypeDef,
    type_var_id::TypeVarKind,
};

pub struct ConstraintSolverSolution {
    pub unsolved_constraints: Vec<Constraint>,
    pub substitutions: Substitutions,
    pub errors: Vec<(ExprID, TypeError)>,
}

pub struct ConstraintSolver<'a> {
    env: &'a mut Environment,
    symbol_table: &'a mut SymbolTable,
    constraints: Vec<Constraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(env: &'a mut Environment, symbol_table: &'a mut SymbolTable) -> Self {
        Self {
            constraints: env.constraints().clone(),
            env,
            symbol_table,
        }
    }

    pub fn solve(&mut self) -> ConstraintSolverSolution {
        let mut substitutions = Substitutions::new();
        let mut errors = vec![];
        let mut unsolved_constraints = vec![];

        while let Some(constraint) = self.constraints.pop() {
            match self.solve_constraint(&constraint, &mut substitutions) {
                Ok(_) => (),
                // Err(TypeError::Defer(_)) => {
                //     if let Constraint::Retry(c, retries) = constraint {
                //         if retries > 0 {
                //             let constraint = c.replacing(&mut substitutions, &mut self.env.context);
                //             self.constraints
                //                 .insert(0, Constraint::Retry(constraint.into(), retries - 1));
                //         } else {
                //             unsolved_constraints.push(*c.clone());
                //         }
                //     } else {
                //         self.constraints.insert(
                //             0,
                //             Constraint::Retry(
                //                 constraint
                //                     .replacing(&mut substitutions, &mut self.env.context)
                //                     .into(),
                //                 3,
                //             ),
                //         );
                //     }
                // }
                Err(err) => {
                    if let Constraint::Retry(constraint, retries) = constraint {
                        if retries > 0 {
                            let constraint =
                                constraint.replacing(&mut substitutions, &mut self.env.context);
                            self.constraints.insert(
                                0,
                                Constraint::Retry(
                                    constraint
                                        .replacing(&mut substitutions, &mut self.env.context)
                                        .into(),
                                    retries - 1,
                                ),
                            );
                        } else {
                            unsolved_constraints.push(*constraint.clone());
                            errors.push((*constraint.expr_id(), err))
                        }
                    } else {
                        self.constraints.insert(
                            0,
                            Constraint::Retry(
                                constraint
                                    .replacing(&mut substitutions, &mut self.env.context)
                                    .into(),
                                3,
                            ),
                        );
                    }
                }
            }
        }

        let mut remaining_type_vars = vec![];

        for (_id, typed_expr) in &mut self.env.typed_exprs.iter_mut() {
            typed_expr.ty = substitutions.apply(&typed_expr.ty, 0, &mut self.env.context);

            if let Ty::TypeVar(var) = &typed_expr.ty {
                remaining_type_vars.push(var.clone());
            }

            // Try to fill in the symbol ID of types of variables
            let this_symbol = match typed_expr.expr {
                Expr::Variable(Name::Resolved(symbol_id, _) | Name::_Self(symbol_id), _) => {
                    symbol_id
                }
                _ => continue,
            };

            let def_symbol = match typed_expr.ty {
                Ty::Struct(struct_id, _) => struct_id,
                Ty::Enum(enum_id, _) => enum_id,
                _ => continue,
            };

            let Some(symbol_info) = self.symbol_table.get_mut(&this_symbol) else {
                continue;
            };

            if let Some(definition) = symbol_info.definition.as_mut() {
                definition.sym = Some(def_symbol);
            }
        }

        // We've applied these constraints, we don't need them anymore.. probably??
        self.constraints.clear();

        ConstraintSolverSolution {
            substitutions,
            errors,
            unsolved_constraints,
        }
    }

    #[tracing::instrument(skip(self, substitutions), fields(result))]
    fn solve_constraint(
        &mut self,
        constraint: &Constraint,
        substitutions: &mut Substitutions,
    ) -> Result<(), TypeError> {
        match &constraint.replacing(substitutions, &mut self.env.context) {
            Constraint::Retry(c, _) => {
                self.solve_constraint(c, substitutions)?;
            }
            Constraint::ConformsTo {
                ty, conformance, ..
            } => {
                if let Ty::TypeVar(type_var) = ty {
                    // There has to be a better way to figure out the conforming type...
                    let types: Vec<_> = self
                        .env
                        .types
                        .values()
                        .filter_map(|t| {
                            let c = t
                                .conformances()
                                .iter()
                                .find(|c| c.protocol_id == conformance.protocol_id)?;

                            if conformance
                                .associated_types
                                .iter()
                                .zip(c.associated_types.iter())
                                .all(|(provided, required)| {
                                    substitutions.unifiable(
                                        provided,
                                        required,
                                        &mut self.env.context,
                                    )
                                })
                            {
                                Some((t.clone(), c.clone()))
                            } else {
                                None
                            }
                            // .map(|c| )
                        })
                        .collect();

                    tracing::warn!("Possible conforming types: {types:?}");

                    let mut conforming_candidates = vec![];
                    for (type_def, type_def_conformance) in types {
                        let type_def_ty = type_def.ty();

                        let conformance_checker =
                            ConformanceChecker::new(&type_def_ty, &type_def_conformance, self.env);
                        match conformance_checker.check() {
                            Ok(unifications) => {
                                conforming_candidates.push((
                                    type_def_ty,
                                    unifications,
                                    type_def_conformance,
                                ));
                            }
                            Err(e) => {
                                tracing::error!("e is {e:?}");
                                continue;
                            }
                        }
                    }

                    match conforming_candidates.len() {
                        0 => {
                            // Not enough info yet
                            return Err(TypeError::Defer(ConformanceError::TypeCannotConform(
                                ty.to_string(),
                            )));
                        }
                        1 => {
                            let (candidate_ty, candidate_unifications, type_def_conformances) =
                                &conforming_candidates[0];

                            // Probably a good bet?
                            substitutions.unify(
                                &Ty::TypeVar(type_var.clone()),
                                candidate_ty,
                                &mut self.env.context,
                            )?;

                            for (provided, required) in conformance
                                .associated_types
                                .iter()
                                .zip(type_def_conformances.associated_types.iter())
                            {
                                substitutions.unify(provided, required, &mut self.env.context)?;
                            }

                            for (lhs, rhs) in candidate_unifications {
                                substitutions.unify(lhs, rhs, &mut self.env.context)?;
                            }

                            return Ok(());
                        }
                        _ => {
                            // Could have conflicting options, shouldn't go for it
                            // Not enough info yet
                            return Err(TypeError::Defer(ConformanceError::TypeCannotConform(
                                ty.to_string(),
                            )));
                        }
                    }
                }

                let conformance_checker = ConformanceChecker::new(ty, conformance, self.env);
                let unifications = conformance_checker.check()?;
                for (lhs, rhs) in unifications {
                    substitutions.unify(&lhs, &rhs, &mut self.env.context)?;
                }
            }
            Constraint::Equality(_node_id, lhs, rhs) => {
                let lhs = substitutions.apply(lhs, 0, &mut self.env.context);
                let rhs = substitutions.apply(rhs, 0, &mut self.env.context);

                substitutions
                    .unify(&lhs, &rhs, &mut self.env.context)
                    .map_err(|err| {
                        tracing::error!("{err:?}");
                        err
                    })?;
            }
            Constraint::InstanceOf { scheme, ty, .. } => {
                let mut mapping = Substitutions::new();
                for unbound_var in &scheme.unbound_vars {
                    mapping.insert(
                        unbound_var.clone(),
                        Ty::TypeVar(self.env.new_type_variable(TypeVarKind::Unbound)),
                    );
                }
                let instantiated_ty = Self::substitute_ty_with_map(ty, &mapping);

                substitutions.unify(ty, &instantiated_ty, &mut self.env.context)?;
            }
            Constraint::UnqualifiedMember(_node_id, member_name, result_ty) => {
                let result_ty = substitutions.apply(result_ty, 0, &mut self.env.context);

                match &result_ty {
                    // A variant with no values
                    Ty::Enum(enum_id, _generics) => {
                        let variant = self
                            .env
                            .lookup_enum(enum_id)
                            .ok_or(TypeError::Unknown(format!(
                                "Unable to resolve enum with id: {enum_id:?}"
                            )))
                            .map(|a| a.tag_with_variant_for(member_name).map(|v| v.1).cloned())?;

                        if let Some(variant) = variant {
                            substitutions.unify(&result_ty, &variant.ty, &mut self.env.context)?;
                        }
                    }
                    // A variant with values
                    Ty::Func(_args, ret, _generics) => {
                        let Ty::Enum(enum_id, _generics) =
                            substitutions.apply(ret, 0, &mut self.env.context)
                        else {
                            tracing::error!(
                                "did not get enum type: {:?}",
                                substitutions.apply(ret, 0, &mut self.env.context)
                            );
                            return Ok(());
                        };

                        // let variant = Ty::EnumVariant(enum_id, args.clone());
                        let variant = self
                            .env
                            .lookup_enum(&enum_id)
                            .ok_or(TypeError::Unknown(format!(
                                "Unable to resolve enum with id: {enum_id:?}"
                            )))
                            .map(|a| a.tag_with_variant_for(member_name).map(|v| v.1).cloned())?;

                        if let Some(variant) = variant {
                            substitutions.unify(&result_ty, &variant.ty, &mut self.env.context)?;
                        }
                    }
                    _ => (),
                }
            }
            Constraint::MemberAccess(_node_id, receiver_ty, member_name, result_ty) => {
                let receiver_ty = substitutions.apply(receiver_ty, 0, &mut self.env.context);
                let result_ty = substitutions.apply(result_ty, 0, &mut self.env.context);

                let (member_ty, type_params, type_args) = match &receiver_ty {
                    builtin @ (Ty::Int | Ty::Float | Ty::Bool | Ty::Pointer) => {
                        #[allow(clippy::expect_used)]
                        let type_def = match builtin {
                            Ty::Int => self.env.lookup_type(&SymbolID::INT),
                            Ty::Float => self.env.lookup_type(&SymbolID::FLOAT),
                            Ty::Bool => self.env.lookup_type(&SymbolID::BOOL),
                            Ty::Pointer => self.env.lookup_type(&SymbolID::POINTER),
                            _ => {
                                return Err(TypeError::Unknown("no idea how this happened".into()));
                            }
                        }
                        .cloned()
                        .expect("builtins should have type defs");

                        let Some(member) =
                            type_def.member_ty_with_conformances(member_name, self.env)
                        else {
                            return Err(TypeError::MemberNotFound(
                                builtin.to_string(),
                                member_name.to_string(),
                            ));
                        };

                        (member, vec![], vec![])
                    }
                    Ty::Struct(type_id, generics) | Ty::Protocol(type_id, generics) => {
                        let type_def = self
                            .env
                            .lookup_type(type_id)
                            .ok_or(TypeError::Unknown(format!(
                                "Unable to resolve enum with id: {type_id:?}"
                            )))?
                            .clone();
                        let Some(member_ty) =
                            type_def.member_ty_with_conformances(member_name, self.env)
                        else {
                            return Err(TypeError::MemberNotFound(
                                type_def.name().to_string(),
                                member_name.to_string(),
                            ));
                        };

                        (
                            member_ty.clone(),
                            type_def.type_parameters().clone(),
                            generics.clone(),
                        )
                    }
                    Ty::Enum(enum_id, generics) => {
                        let enum_def =
                            self.env
                                .lookup_enum(enum_id)
                                .ok_or(TypeError::Unknown(format!(
                                    "Unable to resolve enum with id: {enum_id:?}"
                                )))?;

                        let Some(member_ty) = enum_def.member_ty(member_name) else {
                            return Err(TypeError::Unknown(format!(
                                "Member not found for enum {}: {}",
                                enum_def.name_str, member_name
                            )));
                        };

                        tracing::trace!(
                            "MemberAccess {receiver_ty:?}.{member_name:?} {member_ty:?} -> {result_ty:?} {generics:?}"
                        );

                        (
                            member_ty.clone(),
                            enum_def.type_parameters.clone(),
                            generics.clone(),
                        )
                    }
                    Ty::TypeVar(type_var) => {
                        let matching_constraints = self
                            .constraints
                            .iter()
                            .filter(|constraint| {
                                constraint.contains(|t| *t == Ty::TypeVar(type_var.clone()))
                            })
                            .collect::<Vec<&Constraint>>();

                        let mut result: Option<(Ty, Vec<TypeParameter>, Vec<Ty>)> = None;

                        for constraint in matching_constraints {
                            match constraint {
                                Constraint::ConformsTo { conformance, .. } => {
                                    let Some(TypeDef::Protocol(protocol_def)) =
                                        self.env.lookup_type(&conformance.protocol_id).cloned()
                                    else {
                                        tracing::error!(
                                            "Did not find protocol {:?}",
                                            conformance.protocol_id
                                        );
                                        return Err(TypeError::Unknown(format!(
                                            "did not find protocol with ID: {:?}",
                                            conformance.protocol_id
                                        )));
                                    };

                                    if let Some(ty) = protocol_def.member_ty(member_name) {
                                        result = Some((
                                            ty.clone(),
                                            protocol_def.associated_types,
                                            conformance.associated_types.clone(),
                                        ));

                                        break;
                                    }
                                }
                                Constraint::InstanceOf {
                                    symbol_id, scheme, ..
                                } => {
                                    let Some(type_def) = self.env.lookup_type(symbol_id) else {
                                        continue;
                                    };
                                    let Some(ty) = type_def.member_ty(member_name) else {
                                        return Err(TypeError::MemberNotFound(
                                            member_name.to_string(),
                                            type_def.name().to_string(),
                                        ));
                                    };

                                    let associated_types = scheme
                                        .unbound_vars
                                        .iter()
                                        .map(|t| Ty::TypeVar(t.clone()))
                                        .collect();

                                    result = Some((
                                        ty.clone(),
                                        type_def.type_parameters().clone(),
                                        associated_types,
                                    ));
                                }
                                _ => (),
                            }
                        }

                        if let Some(result) = result {
                            result
                        } else {
                            return Err(TypeError::MemberNotFound(
                                receiver_ty.to_string(),
                                member_name.to_string(),
                            ));
                        }
                    }

                    // Ty::TypeVar(type_var) if !type_var.constraints.is_empty() => {
                    //     let mut result: Option<(Ty, Vec<TypeParameter>, &Vec<Ty>)> = None;

                    //     for constraint in type_var.constraints.iter() {
                    //         match constraint {
                    //             TypeConstraint::InstanceOf {
                    //                 symbol_id,
                    //                 associated_types,
                    //             } => {
                    //                 let Some(type_def) = self.env.lookup_type(symbol_id) else {
                    //                     continue;
                    //                 };
                    //                 let Some(ty) = type_def.member_ty(member_name) else {
                    //                     return Err(TypeError::MemberNotFound(
                    //                         member_name.to_string(),
                    //                         type_def.name().to_string(),
                    //                     ));
                    //                 };
                    //                 result = Some((
                    //                     ty.clone(),
                    //                     type_def.type_parameters().clone(),
                    //                     associated_types,
                    //                 ));
                    //             }
                    //             TypeConstraint::Conforms {
                    //                 protocol_id,
                    //                 associated_types,
                    //             } => {
                    //                 let Some(TypeDef::Protocol(protocol_def)) =
                    //                     self.env.lookup_type(protocol_id).cloned()
                    //                 else {
                    //                     return Err(TypeError::Unknown(format!(
                    //                         "did not find protocol with ID: {protocol_id:?}",
                    //                     )));
                    //                 };

                    //                 if let Some(ty) = protocol_def.member_ty(member_name) {
                    //                     result = Some((
                    //                         ty.clone(),
                    //                         protocol_def.associated_types,
                    //                         associated_types,
                    //                     ));

                    //                     break;
                    //                 }
                    //             }
                    //             TypeConstraint::Equals { .. } => (),
                    //         }
                    //     }

                    //     if let Some(result) = result {
                    //         result
                    //     } else {
                    //         return Err(TypeError::Unknown(format!(
                    //             "Did not find member {member_name} for {receiver_ty:?}"
                    //         )));
                    //     }
                    // }
                    _ => {
                        return Err(TypeError::MemberNotFound(
                            receiver_ty.to_string(),
                            member_name.to_string(),
                        ));
                    }
                };

                let mut member_substitutions = substitutions.clone();
                for (type_param, type_arg) in type_params.iter().zip(type_args) {
                    member_substitutions.insert(type_param.type_var.clone(), type_arg.clone());
                }

                let specialized_ty =
                    Self::substitute_ty_with_map(&member_ty, &member_substitutions);
                substitutions.unify(&result_ty, &specialized_ty, &mut self.env.context)?;
            }
            Constraint::InitializerCall {
                initializes_id,
                args,
                func_ty,
                result_ty,
                ..
            } => {
                let Some(struct_def) = self.env.lookup_struct(initializes_id).cloned() else {
                    return Err(TypeError::Unresolved(
                        "did not find struct def for initialization".into(),
                    ));
                };

                // TODO: Support multiple initializers
                let initializer = &struct_def.initializers[0];
                let Ty::Init(_, params) = &initializer.ty else {
                    unreachable!();
                };

                if args.len() != params.len() {
                    return Err(TypeError::ArgumentError(format!(
                        "Expected {} arguments, got {}",
                        params.len(),
                        args.len()
                    )));
                }

                for (param, arg) in params.iter().zip(args) {
                    let param = &substitutions.apply(param, 0, &mut self.env.context);
                    let arg = &substitutions.apply(arg, 0, &mut self.env.context);

                    substitutions.unify(param, arg, &mut self.env.context)?;
                }

                substitutions.unify(&initializer.ty, func_ty, &mut self.env.context)?;

                let struct_with_generics =
                    Ty::Struct(*initializes_id, struct_def.canonical_type_parameters());

                let specialized_struct = self.env.instantiate(&Scheme::new(
                    struct_with_generics,
                    struct_def.canonical_type_vars(),
                ));

                substitutions.unify(result_ty, &specialized_struct, &mut self.env.context)?;

                // TODO: Make sure we're chill with our conformances
            }
            Constraint::VariantMatch {
                scrutinee_ty,
                variant_name,
                field_tys,
                ..
            } => {
                let scrutinee_ty = substitutions.apply(scrutinee_ty, 0, &mut self.env.context);

                let Ty::Enum(enum_id, concrete_type_args) = &scrutinee_ty else {
                    return Err(TypeError::Unknown(format!(
                        "VariantMatch expected an enum, but got {scrutinee_ty:?}"
                    )));
                };

                let Some(enum_def) = self.env.lookup_enum(enum_id) else {
                    unreachable!("Enum definition not found for a typed enum.");
                };

                let Some(variant_def) = enum_def.variants.iter().find(|v| v.name == *variant_name)
                else {
                    return Err(TypeError::UnknownVariant(Name::Raw(variant_name.clone())));
                };

                // Extract the generic field types from the variant's definition (e.g., `[T]` for `some(T)`).
                let Ty::EnumVariant(_, generic_field_tys) = &variant_def.ty else {
                    unreachable!("Variant's type is not an EnumVariant.");
                };

                // Create a substitution map to specialize the variant's types.
                // This maps the enum's generic parameters (e.g., T) to the scrutinee's concrete types (e.g., Int).
                let mut local_substitutions = Substitutions::new();
                for (type_param, concrete_arg) in
                    enum_def.type_parameters.iter().zip(concrete_type_args)
                {
                    local_substitutions.insert(type_param.type_var.clone(), concrete_arg.clone());
                }

                // Specialize the variant's generic field types using the local map.
                // This turns `[T]` into `[Int]`.
                let specialized_field_tys = generic_field_tys
                    .iter()
                    .map(|ty| Self::substitute_ty_with_map(ty, &local_substitutions))
                    .collect::<Vec<_>>();

                // Now, unify the specialized, concrete field types with the types from the pattern.
                if specialized_field_tys.len() != field_tys.len() {
                    return Err(TypeError::Unknown(
                        "Variant pattern has incorrect number of fields.".into(),
                    ));
                }

                for (specialized_ty, pattern_ty) in specialized_field_tys.iter().zip(field_tys) {
                    substitutions.unify(specialized_ty, pattern_ty, &mut self.env.context)?;
                }
            }
        };

        Ok(())
    }

    /// Applies a given substitution map to a type. Does not recurse on type variables already in the map.
    #[tracing::instrument(fields(result))]
    pub fn substitute_ty_with_map(ty: &Ty, substitutions: &Substitutions) -> Ty {
        match ty {
            Ty::TypeVar(type_var_id) => {
                if let Some(substituted_ty) = substitutions.get(type_var_id) {
                    substituted_ty.clone()
                } else {
                    ty.clone() // Not in this substitution map, return as is.
                }
            }
            Ty::Init(struct_id, params) => {
                let applied_params = params
                    .iter()
                    .map(|param| Self::substitute_ty_with_map(param, substitutions))
                    .collect();

                Ty::Init(*struct_id, applied_params)
            }
            Ty::Func(params, returning, generics) => {
                let applied_params = params
                    .iter()
                    .map(|param| Self::substitute_ty_with_map(param, substitutions))
                    .collect();
                let applied_return = Self::substitute_ty_with_map(returning, substitutions);
                let applied_generics = generics
                    .iter()
                    .map(|g| Self::substitute_ty_with_map(g, substitutions))
                    .collect();
                Ty::Func(applied_params, Box::new(applied_return), applied_generics)
            }
            Ty::Closure { func, captures } => {
                let func = Self::substitute_ty_with_map(func, substitutions)
                    .clone()
                    .into();

                Ty::Closure {
                    func,
                    captures: captures.clone(),
                }
            }
            Ty::Enum(name, generics) => {
                let applied_generics = generics
                    .iter()
                    .map(|g| Self::substitute_ty_with_map(g, substitutions))
                    .collect();
                Ty::Enum(*name, applied_generics)
            }
            Ty::EnumVariant(enum_id, values) => {
                let applied_values = values
                    .iter()
                    .map(|v| Self::substitute_ty_with_map(v, substitutions))
                    .collect();
                Ty::EnumVariant(*enum_id, applied_values)
            }
            Ty::Tuple(types) => Ty::Tuple(
                types
                    .iter()
                    .map(|param| Self::substitute_ty_with_map(param, substitutions))
                    .collect(),
            ),
            Ty::Array(ty) => Ty::Array(Self::substitute_ty_with_map(ty, substitutions).into()),
            Ty::Struct(sym, generics) => Ty::Struct(
                *sym,
                generics
                    .iter()
                    .map(|t| Self::substitute_ty_with_map(t, substitutions))
                    .collect(),
            ),
            Ty::Protocol(sym, generics) => Ty::Protocol(
                *sym,
                generics
                    .iter()
                    .map(|t| Self::substitute_ty_with_map(t, substitutions))
                    .collect(),
            ),
            Ty::Void | Ty::Pointer | Ty::Int | Ty::Float | Ty::Bool | Ty::SelfType | Ty::Byte => {
                ty.clone()
            }
        }
    }
}
