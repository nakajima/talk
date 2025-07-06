use std::collections::HashMap;

use crate::{
    SymbolID, SymbolTable,
    conformance_checker::{ConformanceChecker, ConformanceError},
    constraint::{Constraint, Substitutions},
    environment::{Environment, TypeParameter},
    expr::Expr,
    name::Name,
    parser::ExprID,
    satisfies_checker::SatisfiesChecker,
    ty::Ty,
    type_checker::TypeError,
    type_defs::TypeDef,
    type_var_id::{TypeVarID, TypeVarKind},
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
        let mut substitutions = HashMap::<TypeVarID, Ty>::new();
        let mut errors = vec![];
        let mut unsolved_constraints = vec![];

        while let Some(constraint) = self.constraints.pop() {
            match self.solve_constraint(&constraint, &mut substitutions) {
                Ok(_) => (),
                Err(TypeError::Defer(_)) => {
                    if let Constraint::Retry(c, retries) = constraint {
                        if retries > 0 {
                            let constraint = c.replacing(&substitutions);
                            self.constraints
                                .insert(0, Constraint::Retry(constraint.into(), retries - 1));
                        } else {
                            unsolved_constraints.push(*c.clone());
                        }
                    } else {
                        self.constraints.insert(
                            0,
                            Constraint::Retry(constraint.replacing(&substitutions).into(), 3),
                        );
                    }
                }
                Err(err) => {
                    if let Constraint::Retry(constraint, retries) = constraint {
                        if retries > 0 {
                            let constraint = constraint.replacing(&substitutions);
                            tracing::trace!(
                                "Retrying {constraint:?} ({retries} remaining (subs {})) {substitutions:?}",
                                substitutions.len()
                            );
                            self.constraints.insert(
                                0,
                                Constraint::Retry(
                                    constraint.replacing(&substitutions).into(),
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
                            Constraint::Retry(constraint.replacing(&substitutions).into(), 3),
                        );
                    }
                }
            }
        }

        let mut remaining_type_vars = vec![];

        for (_id, typed_expr) in &mut self.env.typed_exprs.iter_mut() {
            typed_expr.ty = Self::apply(&typed_expr.ty, &substitutions, 0);

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
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), TypeError> {
        tracing::info!(
            "Solving constraint: {:?}",
            constraint.replacing(substitutions)
        );
        match &constraint.replacing(substitutions) {
            Constraint::Retry(c, _) => {
                self.solve_constraint(c, substitutions)?;
            }
            Constraint::ConformsTo {
                ty, conformance, ..
            } => {
                if matches!(ty, Ty::TypeVar(_)) {
                    // Not enough info yet
                    return Err(TypeError::Defer(ConformanceError::TypeCannotConform(
                        ty.to_string(),
                    )));
                }

                let conformance_checker = ConformanceChecker::new(ty, conformance, self.env);
                let unifications = conformance_checker.check()?;
                for (lhs, rhs) in unifications {
                    self.unify(&lhs, &rhs, substitutions)?;
                }
                Self::normalize_substitutions(substitutions);
            }
            Constraint::Equality(_node_id, lhs, rhs) => {
                let lhs = Self::apply(lhs, substitutions, 0);
                let rhs = Self::apply(rhs, substitutions, 0);

                self.unify(&lhs, &rhs, substitutions).map_err(|err| {
                    tracing::error!("{err:?}");
                    err
                })?;

                Self::normalize_substitutions(substitutions);
            }
            Constraint::InstanceOf { scheme, ty, .. } => {
                let mut mapping = HashMap::new();
                for unbound_var in &scheme.unbound_vars {
                    mapping.insert(
                        unbound_var.clone(),
                        Ty::TypeVar(self.env.new_type_variable(TypeVarKind::Unbound)),
                    );
                }
                let instantiated_ty = Self::substitute_ty_with_map(ty, &mapping);

                self.unify(ty, &instantiated_ty, substitutions)?;
                Self::normalize_substitutions(substitutions);
            }
            Constraint::UnqualifiedMember(_node_id, member_name, result_ty) => {
                let result_ty = Self::apply(result_ty, substitutions, 0);

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
                            self.unify(&result_ty, &variant.ty, substitutions)?;
                        }
                    }
                    // A variant with values
                    Ty::Func(_args, ret, _generics) => {
                        let Ty::Enum(enum_id, _generics) = Self::apply(ret, substitutions, 0)
                        else {
                            tracing::error!(
                                "did not get enum type: {:?}",
                                Self::apply(ret, substitutions, 0)
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
                            self.unify(&result_ty, &variant.ty, substitutions)?;
                        }
                    }
                    _ => (),
                }
            }
            Constraint::Satisfies {
                ty, constraints, ..
            } => {
                let ty = Self::apply(ty, substitutions, 0);
                let checker = SatisfiesChecker::new(self.env, &ty, constraints);
                let unifications = checker.check()?;
                for (lhs, rhs) in unifications {
                    self.unify(&lhs, &rhs, substitutions)?;
                }
            }
            Constraint::MemberAccess(_node_id, receiver_ty, member_name, result_ty) => {
                let receiver_ty = Self::apply(receiver_ty, substitutions, 0);
                let result_ty = Self::apply(result_ty, substitutions, 0);

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
                self.unify(&result_ty, &specialized_ty, substitutions)?;
                Self::normalize_substitutions(substitutions);
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
                    self.unify(param, arg, substitutions)?;
                }

                self.unify(&initializer.ty, func_ty, substitutions)?;

                let struct_with_generics =
                    Ty::Struct(*initializes_id, struct_def.canonical_type_parameters());

                let specialized_struct = Self::apply(&struct_with_generics, substitutions, 0);

                self.unify(result_ty, &specialized_struct, substitutions)?;

                Self::normalize_substitutions(substitutions);
            }
            Constraint::VariantMatch {
                scrutinee_ty,
                variant_name,
                field_tys,
                ..
            } => {
                let scrutinee_ty = Self::apply(scrutinee_ty, substitutions, 0);

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
                let mut local_substitutions = HashMap::new();
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
                    self.unify(specialized_ty, pattern_ty, substitutions)?;
                }

                Self::normalize_substitutions(substitutions);
            }
        };

        Ok(())
    }

    fn apply_multiple(types: &[Ty], substitutions: &HashMap<TypeVarID, Ty>, depth: u32) -> Vec<Ty> {
        types
            .iter()
            .map(|ty| Self::apply(ty, substitutions, depth))
            .collect()
    }

    pub fn apply(ty: &Ty, substitutions: &HashMap<TypeVarID, Ty>, depth: u32) -> Ty {
        if depth > 20 {
            tracing::error!("Hit 100 recursive applications for {ty:#?}, bailing.");
            return ty.clone();
        }

        // tracing::trace!("Applying:\n{:#?}\n---\n{:?}", ty, substitutions);

        match ty {
            Ty::Pointer => ty.clone(),
            Ty::Int => ty.clone(),
            Ty::Byte => ty.clone(),
            Ty::Float => ty.clone(),
            Ty::Bool => ty.clone(),
            Ty::SelfType => ty.clone(),
            Ty::Func(params, returning, generics) => {
                let applied_params = Self::apply_multiple(params, substitutions, depth + 1);
                let applied_return = Self::apply(returning, substitutions, depth + 1);
                let applied_generics = Self::apply_multiple(generics, substitutions, depth + 1);

                Ty::Func(applied_params, Box::new(applied_return), applied_generics)
            }
            Ty::TypeVar(type_var) => {
                if let Some(ty) = substitutions.get(type_var) {
                    Self::apply(ty, substitutions, depth + 1)
                } else if let TypeVarID {
                    kind: TypeVarKind::Instantiated(i),
                    ..
                } = type_var
                {
                    let parent_type_var =
                        TypeVarID::new(*i, TypeVarKind::Canonicalized(type_var.id));
                    Self::apply(&Ty::TypeVar(parent_type_var), substitutions, depth + 1)
                } else if let TypeVarID {
                    kind: TypeVarKind::Canonicalized(i),
                    ..
                } = type_var
                {
                    Ty::TypeVar(TypeVarID::new(*i, TypeVarKind::Instantiated(type_var.id)))
                } else {
                    ty.clone()
                }
            }
            Ty::Enum(name, generics) => {
                let applied_generics = Self::apply_multiple(generics, substitutions, depth + 1);

                Ty::Enum(*name, applied_generics)
            }
            Ty::EnumVariant(enum_id, values) => {
                let applied_values = values
                    .iter()
                    .map(|variant| Self::apply(variant, substitutions, depth + 1))
                    .collect();
                Ty::EnumVariant(*enum_id, applied_values)
            }
            Ty::Tuple(types) => Ty::Tuple(
                types
                    .iter()
                    .map(|variant| Self::apply(variant, substitutions, depth + 1))
                    .collect(),
            ),
            Ty::Closure { func, captures } => {
                let func = Self::apply(func, substitutions, depth + 1).into();
                Ty::Closure {
                    func,
                    captures: captures.clone(),
                }
            }
            Ty::Array(ty) => Ty::Array(Self::apply(ty, substitutions, depth + 1).into()),
            Ty::Struct(sym, generics) => Ty::Struct(
                *sym,
                Self::apply_multiple(generics, substitutions, depth + 1),
            ),
            Ty::Protocol(sym, generics) => Ty::Protocol(
                *sym,
                Self::apply_multiple(generics, substitutions, depth + 1),
            ),
            Ty::Init(struct_id, params) => Ty::Init(
                *struct_id,
                Self::apply_multiple(params, substitutions, depth + 1),
            ),
            Ty::Void => ty.clone(),
        }
    }

    fn normalize_substitutions(substitutions: &mut HashMap<TypeVarID, Ty>) {
        let mut changed = true;
        while changed {
            changed = false;
            let mut updates = Vec::new();

            for (var_id, ty) in substitutions.iter() {
                let normalized = Self::apply(ty, substitutions, 0);
                if &normalized != ty {
                    updates.push((var_id.clone(), normalized));
                    changed = true;
                }
            }

            for (var_id, new_ty) in updates {
                substitutions.insert(var_id, new_ty);
            }
        }
    }

    pub fn unify(
        &mut self,
        lhs: &Ty,
        rhs: &Ty,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), TypeError> {
        if lhs == rhs {
            return Ok(());
        }

        let res = match (
            Self::apply(lhs, substitutions, 0),
            Self::apply(rhs, substitutions, 0),
        ) {
            // They're the same, sick.
            (a, b) if a == b => Ok(()),

            (Ty::TypeVar(v1), Ty::TypeVar(v2)) => {
                // When unifying two type variables, pick one consistently, favoring more constraints
                if v1.id < v2.id {
                    let id = TypeVarID::new(v1.id, v1.kind);
                    substitutions.insert(v2.clone(), Ty::TypeVar(id));
                } else {
                    let id = TypeVarID::new(v2.id, v2.kind);
                    substitutions.insert(v1.clone(), Ty::TypeVar(id));
                }

                Self::normalize_substitutions(substitutions);
                Ok(())
            }

            (Ty::TypeVar(v), ty) | (ty, Ty::TypeVar(v)) => {
                if let TypeVarKind::CanonicalTypeParameter(_) = &v.kind {
                    tracing::warn!(
                        "Attempting to unify canonical type parameter {v:?} with {ty:?}. Consider instantiating."
                    );
                }

                if Self::occurs_check(&v, &ty, substitutions) {
                    Err(TypeError::OccursConflict)
                } else {
                    substitutions.insert(v.clone(), ty.clone());
                    Self::normalize_substitutions(substitutions);
                    Ok(())
                }
            }
            (
                Ty::Func(lhs_params, lhs_returning, lhs_gen),
                Ty::Func(rhs_params, rhs_returning, rhs_gen),
            ) if lhs_params.len() == rhs_params.len() => {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    self.unify(lhs, &rhs, substitutions)?;
                }

                for (lhs, rhs) in lhs_gen.iter().zip(rhs_gen) {
                    self.unify(lhs, &rhs, substitutions)?;
                }

                self.unify(&lhs_returning, &rhs_returning, substitutions)?;
                Self::normalize_substitutions(substitutions);

                Ok(())
            }
            (Ty::Closure { func: lhs_func, .. }, Ty::Closure { func: rhs_func, .. }) => {
                self.unify(&lhs_func, &rhs_func, substitutions)?;
                Self::normalize_substitutions(substitutions);
                Ok(())
            }
            (func, Ty::Closure { func: closure, .. })
            | (Ty::Closure { func: closure, .. }, func)
                if matches!(func, Ty::Func(_, _, _)) =>
            {
                self.unify(&func, &closure, substitutions)?;
                Self::normalize_substitutions(substitutions);
                Ok(())
            }
            (Ty::Enum(_, lhs_types), Ty::Enum(_, rhs_types))
                if lhs_types.len() == rhs_types.len() =>
            {
                for (lhs, rhs) in lhs_types.iter().zip(rhs_types) {
                    self.unify(lhs, &rhs, substitutions)?;
                    Self::normalize_substitutions(substitutions);
                }

                Ok(())
            }
            (Ty::Enum(_, enum_types), Ty::EnumVariant(_, variant_types))
            | (Ty::EnumVariant(_, variant_types), Ty::Enum(_, enum_types)) => {
                for (e_ty, v_ty) in enum_types.iter().zip(variant_types) {
                    self.unify(e_ty, &v_ty, substitutions)?;
                }

                Ok(())
            }
            (Ty::Struct(_, lhs), Ty::Struct(_, rhs)) if lhs.len() == rhs.len() => {
                for (lhs, rhs) in lhs.iter().zip(rhs) {
                    self.unify(lhs, &rhs, substitutions)?;
                    Self::normalize_substitutions(substitutions);
                }

                Ok(())
            }
            (Ty::Func(func_args, ret, generics), Ty::EnumVariant(enum_id, variant_args))
            | (Ty::EnumVariant(enum_id, variant_args), Ty::Func(func_args, ret, generics))
                if func_args.len() == variant_args.len() =>
            {
                // We always want the return value to be the enum
                let Some(enum_def) = self.env.lookup_enum(&enum_id) else {
                    return Err(TypeError::Unknown(
                        "Didn't find enum def for {enum_id:?}".into(),
                    ));
                };

                let mut member_substitutions = substitutions.clone();
                for (type_param, type_arg) in enum_def.type_parameters.iter().zip(generics) {
                    tracing::trace!("Member substitution: {type_param:?} -> {type_arg:?}");
                    member_substitutions.insert(type_param.type_var.clone(), type_arg.clone());
                }
                let specialized_ty = Self::substitute_ty_with_map(
                    &Ty::EnumVariant(enum_id, func_args),
                    substitutions,
                );

                self.unify(&ret, &specialized_ty, substitutions)?;
                Self::normalize_substitutions(substitutions);

                Ok(())
            }
            _ => {
                tracing::error!(
                    "Mismatch: {:?} and {:?}",
                    Self::apply(lhs, substitutions, 0),
                    Self::apply(rhs, substitutions, 0)
                );
                Err(TypeError::Mismatch(
                    Self::apply(lhs, substitutions, 0).to_string(),
                    Self::apply(rhs, substitutions, 0).to_string(),
                ))
            }
        };

        tracing::debug!(
            "∪ {:?} <> {:?} = {:?} <> {:?}",
            lhs,
            rhs,
            Self::apply(lhs, substitutions, 0),
            Self::apply(rhs, substitutions, 0)
        );

        res
    }

    /// Returns true if `v` occurs inside `ty`
    fn occurs_check(v: &TypeVarID, ty: &Ty, substitutions: &HashMap<TypeVarID, Ty>) -> bool {
        let ty = Self::apply(ty, substitutions, 0);
        match &ty {
            Ty::TypeVar(tv) => tv == v,
            Ty::Func(params, returning, generics)
            | Ty::Closure {
                func: box Ty::Func(params, returning, generics),
                ..
            } => {
                // check each parameter and the return type
                let oh = params
                    .iter()
                    .any(|param| Self::occurs_check(v, param, substitutions))
                    || Self::occurs_check(v, returning, substitutions)
                    || generics
                        .iter()
                        .any(|generic| Self::occurs_check(v, generic, substitutions));
                if oh {
                    tracing::error!("occur check failed: {ty:?}");
                }

                oh
            }
            Ty::Enum(_name, generics) => generics
                .iter()
                .any(|generic| Self::occurs_check(v, generic, substitutions)),
            Ty::EnumVariant(_enum_id, values) => values
                .iter()
                .any(|value| Self::occurs_check(v, value, substitutions)),
            _ => false,
        }
    }

    /// Applies a given substitution map to a type. Does not recurse on type variables already in the map.
    pub fn substitute_ty_with_map(ty: &Ty, substitutions: &HashMap<TypeVarID, Ty>) -> Ty {
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
