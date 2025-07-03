use std::collections::HashMap;

use crate::{
    NameResolved, Phase, SourceFile, SymbolID, SymbolTable,
    compiling::compilation_session::SharedCompilationSession,
    conformance_checker::ConformanceChecker,
    diagnostic::Diagnostic,
    environment::{Environment, TypeParameter},
    expr::Expr,
    name::Name,
    parser::ExprID,
    satisfies_checker::SatisfiesChecker,
    ty::Ty,
    type_checker::{Scheme, TypeError},
    type_constraint::TypeConstraint,
    type_defs::{TypeDef, protocol_def::Conformance},
    type_var_id::{TypeVarID, TypeVarKind},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    Equality(ExprID, Ty, Ty),
    MemberAccess(ExprID, Ty, String, Ty), // receiver_ty, member_name, result_ty
    UnqualifiedMember(ExprID, String, Ty), // member name, expected type
    InitializerCall {
        expr_id: ExprID,
        initializes_id: SymbolID,
        args: Vec<Ty>,
        func_ty: Ty,
        result_ty: Ty,
    },
    VariantMatch {
        expr_id: ExprID,
        scrutinee_ty: Ty, // The type of the value being matched (the `expected` type)
        variant_name: String,
        // The list of fresh TypeVars created for each field in the pattern.
        field_tys: Vec<Ty>,
    },
    InstanceOf {
        scheme: Scheme,
        expr_id: ExprID,
        ty: Ty,
        symbol_id: SymbolID,
    },
    ConformsTo {
        expr_id: ExprID,
        type_def: SymbolID,
        conformance: Conformance,
    },
    Satisfies {
        expr_id: ExprID,
        ty: Ty,
        constraints: Vec<TypeConstraint>,
    },
    Retry(Box<Constraint>),
}

pub type Substitutions = HashMap<TypeVarID, Ty>;

impl Constraint {
    fn expr_id(&self) -> &ExprID {
        match self {
            Self::Equality(id, _, _) => id,
            Self::MemberAccess(id, _, _, _) => id,
            Self::UnqualifiedMember(id, _, _) => id,
            Self::InitializerCall { expr_id, .. } => expr_id,
            Self::VariantMatch { expr_id, .. } => expr_id,
            Self::InstanceOf { expr_id, .. } => expr_id,
            Self::ConformsTo { expr_id, .. } => expr_id,
            Self::Satisfies { expr_id, .. } => expr_id,
            Self::Retry(c) => c.expr_id(),
        }
    }

    pub fn replacing(&self, substitutions: &HashMap<TypeVarID, Ty>) -> Constraint {
        match self {
            Constraint::Equality(id, ty, ty1) => Constraint::Equality(
                *id,
                ConstraintSolver::<NameResolved>::apply(ty, substitutions, 0),
                ConstraintSolver::<NameResolved>::apply(ty1, substitutions, 0),
            ),
            Constraint::MemberAccess(id, ty, name, ty1) => Constraint::MemberAccess(
                *id,
                ConstraintSolver::<NameResolved>::apply(ty, substitutions, 0),
                name.clone(),
                ConstraintSolver::<NameResolved>::apply(ty1, substitutions, 0),
            ),
            Constraint::UnqualifiedMember(id, name, ty) => Constraint::UnqualifiedMember(
                *id,
                name.clone(),
                ConstraintSolver::<NameResolved>::apply(ty, substitutions, 0),
            ),
            Constraint::InitializerCall {
                expr_id,
                initializes_id,
                args,
                func_ty,
                result_ty,
            } => Constraint::InitializerCall {
                expr_id: *expr_id,
                initializes_id: *initializes_id,
                args: args
                    .iter()
                    .map(|a| ConstraintSolver::<NameResolved>::apply(a, substitutions, 0))
                    .collect(),
                func_ty: ConstraintSolver::<NameResolved>::apply(func_ty, substitutions, 0),
                result_ty: ConstraintSolver::<NameResolved>::apply(result_ty, substitutions, 0),
            },
            Constraint::VariantMatch {
                expr_id,
                scrutinee_ty,
                variant_name,
                field_tys,
            } => Constraint::VariantMatch {
                expr_id: *expr_id,
                scrutinee_ty: ConstraintSolver::<NameResolved>::apply(
                    scrutinee_ty,
                    substitutions,
                    0,
                ),
                variant_name: variant_name.clone(),
                field_tys: field_tys
                    .iter()
                    .map(|ty| ConstraintSolver::<NameResolved>::apply(ty, substitutions, 0))
                    .collect(),
            },
            Constraint::InstanceOf {
                expr_id,
                ty,
                symbol_id,
                scheme,
            } => Constraint::InstanceOf {
                expr_id: *expr_id,
                ty: ConstraintSolver::<NameResolved>::apply(ty, substitutions, 0),
                symbol_id: *symbol_id,
                scheme: Scheme {
                    ty: ConstraintSolver::<NameResolved>::apply(&scheme.ty, substitutions, 0),
                    unbound_vars: scheme.unbound_vars.clone(),
                },
            },
            constraint @ Constraint::ConformsTo { .. } => constraint.clone(),
            Constraint::Satisfies {
                expr_id,
                ty,
                constraints,
            } => Constraint::Satisfies {
                expr_id: *expr_id,
                ty: ConstraintSolver::<NameResolved>::apply(ty, substitutions, 0),
                constraints: constraints.clone(),
            },
            Constraint::Retry(c) => c.replacing(substitutions).clone(),
        }
    }
}

pub struct ConstraintSolver<'a, P: Phase = NameResolved> {
    source_file: &'a mut SourceFile<P>,
    env: &'a mut Environment,
    symbol_table: &'a mut SymbolTable,
    constraints: Vec<Constraint>,
    session: SharedCompilationSession,
}

impl<'a, P: Phase> ConstraintSolver<'a, P> {
    pub fn new(
        session: SharedCompilationSession,
        source_file: &'a mut SourceFile<P>,
        env: &'a mut Environment,
        symbol_table: &'a mut SymbolTable,
    ) -> Self {
        Self {
            constraints: env.constraints().clone(),
            env,
            source_file,
            symbol_table,
            session,
        }
    }

    fn add_diagnostic(&self, diagnostic: Diagnostic) {
        if let Ok(mut lock) = self.session.lock() {
            lock.add_diagnostic(diagnostic)
        }
    }

    pub fn solve(&mut self) -> HashMap<TypeVarID, Ty> {
        let mut substitutions = HashMap::<TypeVarID, Ty>::new();

        while let Some(constraint) = self.constraints.pop() {
            match self.solve_constraint(&constraint, &mut substitutions, false) {
                Ok(_) => (),
                Err(err) => {
                    self.add_diagnostic(Diagnostic::typing(
                        self.source_file.path.clone(),
                        *constraint.expr_id(),
                        err,
                    ));
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

        substitutions
    }

    fn solve_constraint(
        &mut self,
        constraint: &Constraint,
        substitutions: &mut HashMap<TypeVarID, Ty>,
        is_retry: bool,
    ) -> Result<(), TypeError> {
        log::info!(
            "Solving constraint: {:?}",
            constraint.replacing(substitutions)
        );
        match &constraint.replacing(substitutions) {
            Constraint::Retry(c) => {
                self.solve_constraint(c, substitutions, true)?;
            }
            Constraint::ConformsTo {
                expr_id,
                type_def,
                conformance,
            } => {
                let Some(type_def) = self.env.lookup_type(type_def) else {
                    return Err(TypeError::Unknown(format!(
                        "could not find type: {type_def:?}"
                    )));
                };

                let Some(TypeDef::Protocol(protocol)) =
                    self.env.lookup_type(&conformance.protocol_id)
                else {
                    return Err(TypeError::Unknown(format!(
                        "could not find protocol: {conformance:?}"
                    )));
                };

                let conformance_checker = ConformanceChecker::new(type_def, protocol);
                match conformance_checker.check() {
                    Ok(unifications) => {
                        for (lhs, rhs) in unifications {
                            self.unify(&lhs, &rhs, substitutions)?;
                        }
                        Self::normalize_substitutions(substitutions);
                    }
                    Err(err) => {
                        self.add_diagnostic(Diagnostic::typing(
                            self.source_file.path.clone(),
                            *expr_id,
                            err,
                        ));
                    }
                }
            }
            Constraint::Equality(_node_id, lhs, rhs) => {
                let lhs = Self::apply(lhs, substitutions, 0);
                let rhs = Self::apply(rhs, substitutions, 0);

                self.unify(&lhs, &rhs, substitutions).map_err(|err| {
                    log::error!("{err:?}");
                    err
                })?;

                Self::normalize_substitutions(substitutions);
            }
            Constraint::InstanceOf { scheme, ty, .. } => {
                let mut mapping = HashMap::new();
                for unbound_var in &scheme.unbound_vars {
                    mapping.insert(
                        unbound_var.clone(),
                        Ty::TypeVar(self.env.new_type_variable(
                            TypeVarKind::Unbound,
                            unbound_var.constraints.clone(),
                        )),
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
                            .map(|a| a.tag_with_variant_for(member_name).map(|v| v.1))?;

                        if let Some(variant) = variant {
                            self.unify(&result_ty, &variant.ty, substitutions)?;
                        }
                    }
                    // A variant with values
                    Ty::Func(_args, ret, _generics) => {
                        let Ty::Enum(enum_id, _generics) = Self::apply(ret, substitutions, 0)
                        else {
                            println!(
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
                            .map(|a| a.tag_with_variant_for(member_name).map(|v| v.1))?;

                        if let Some(variant) = variant {
                            self.unify(&result_ty, &variant.ty, substitutions)?;
                        }
                    }
                    _ => (),
                }
            }
            Constraint::Satisfies {
                expr_id,
                ty,
                constraints,
                ..
            } => {
                let checker = SatisfiesChecker::new(self.env, ty, constraints);
                match checker.check() {
                    Ok(unifications) => {
                        for (lhs, rhs) in unifications {
                            self.unify(&lhs, &rhs, substitutions)?;
                        }
                    }
                    Err(err) => {
                        self.add_diagnostic(Diagnostic::typing(
                            self.source_file.path.clone(),
                            *expr_id,
                            err,
                        ));
                    }
                }
            }
            Constraint::MemberAccess(_node_id, receiver_ty, member_name, result_ty) => {
                let receiver_ty = Self::apply(receiver_ty, substitutions, 0);
                let result_ty = Self::apply(result_ty, substitutions, 0);

                let (member_ty, type_params, type_args) = match &receiver_ty {
                    Ty::Struct(type_id, generics) | Ty::Protocol(type_id, generics) => {
                        let type_def = self
                            .env
                            .lookup_type(type_id)
                            .ok_or(TypeError::Unknown(format!(
                                "Unable to resolve enum with id: {type_id:?}"
                            )))?
                            .clone();
                        let mut member_ty_search = type_def.member_ty(member_name).cloned();

                        if member_ty_search.is_none() {
                            for conformance in type_def.conformances() {
                                if let Some(TypeDef::Protocol(protocol_def)) =
                                    self.env.lookup_type(&conformance.protocol_id).cloned()
                                    && let Some(ty) = protocol_def.member_ty(member_name)
                                {
                                    let mut subst = HashMap::new();
                                    for (param, arg) in protocol_def
                                        .associated_types
                                        .iter()
                                        .zip(&conformance.associated_types)
                                    {
                                        subst.insert(param.type_var.clone(), arg.clone());
                                    }
                                    member_ty_search =
                                        Some(Self::substitute_ty_with_map(ty, &subst));
                                    break;
                                }
                            }
                        }

                        let Some(member_ty) = member_ty_search else {
                            return Err(TypeError::MemberNotFound(
                                member_name.to_string(),
                                type_def.name().to_string(),
                            ));
                        };

                        log::trace!(
                            "MemberAccess {receiver_ty:?}.{member_name:?} {member_ty:?} -> {result_ty:?} {generics:?}"
                        );

                        (
                            member_ty.clone(),
                            type_def.type_parameters().clone(),
                            generics,
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

                        log::trace!(
                            "MemberAccess {receiver_ty:?}.{member_name:?} {member_ty:?} -> {result_ty:?} {generics:?}"
                        );

                        (
                            member_ty.clone(),
                            enum_def.type_parameters.clone(),
                            generics,
                        )
                    }
                    Ty::TypeVar(type_var) if !type_var.constraints.is_empty() => {
                        let mut result: Option<(Ty, Vec<TypeParameter>, &Vec<Ty>)> = None;

                        for constraint in type_var.constraints.iter() {
                            match constraint {
                                TypeConstraint::InstanceOf {
                                    symbol_id,
                                    associated_types,
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
                                    result = Some((
                                        ty.clone(),
                                        type_def.type_parameters().clone(),
                                        associated_types,
                                    ));
                                }
                                TypeConstraint::Conforms {
                                    protocol_id,
                                    associated_types,
                                } => {
                                    let Some(TypeDef::Protocol(protocol_def)) =
                                        self.env.lookup_type(protocol_id).cloned()
                                    else {
                                        return Err(TypeError::Unknown(format!(
                                            "did not find protocol with ID: {protocol_id:?}",
                                        )));
                                    };

                                    if let Some(ty) = protocol_def.member_ty(member_name) {
                                        result = Some((
                                            ty.clone(),
                                            protocol_def.associated_types,
                                            associated_types,
                                        ));

                                        break;
                                    }
                                }
                                TypeConstraint::Equals { .. } => (),
                            }
                        }

                        if let Some(result) = result {
                            result
                        } else {
                            return Err(TypeError::Unknown(format!(
                                "Did not find member {member_name} for {receiver_ty:?}"
                            )));
                        }
                    }
                    _ => {
                        // todo!(
                        //     "{:?} {:?}",
                        //     Self::apply(&receiver_ty, substitutions, 0),
                        //     Self::apply(&result_ty, substitutions, 0)
                        // );
                        if !is_retry && !matches!(constraint, Constraint::Retry(_)) {
                            log::warn!("Pushing retry {constraint:?}");

                            self.constraints
                                .push(Constraint::Retry(constraint.clone().into()));
                            return Ok(());
                        } else {
                            log::error!("Retry failed for {constraint:?}");
                            return Err(TypeError::Unknown(format!(
                                "Retry failed for: {constraint:?}",
                            )));
                        }
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
                let Some(struct_def) = self.env.lookup_struct(initializes_id) else {
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
            log::error!("Hit 100 recursive applications for {ty:#?}, bailing.");
            return ty.clone();
        }

        // log::trace!("Applying:\n{:#?}\n---\n{:?}", ty, substitutions);

        match ty {
            Ty::Pointer => ty.clone(),
            Ty::Int => ty.clone(),
            Ty::Float => ty.clone(),
            Ty::Bool => ty.clone(),
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
                    let parent_type_var = TypeVarID::new(
                        *i,
                        TypeVarKind::Canonicalized(type_var.id),
                        type_var.constraints.clone(),
                    );
                    Self::apply(&Ty::TypeVar(parent_type_var), substitutions, depth + 1)
                } else if let TypeVarID {
                    kind: TypeVarKind::Canonicalized(i),
                    ..
                } = type_var
                {
                    Ty::TypeVar(TypeVarID::new(
                        *i,
                        TypeVarKind::Instantiated(type_var.id),
                        type_var.constraints.clone(),
                    ))
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
        &self,
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
                let combined_constraints =
                    [v1.constraints.clone(), v2.constraints.clone()].concat();

                if !combined_constraints.is_empty() {
                    log::trace!(
                        "Combined constraints: {v1:?} <> {v2:?} = {combined_constraints:?}"
                    );
                };

                // When unifying two type variables, pick one consistently
                if v1.id < v2.id {
                    let id = TypeVarID::new(v1.id, v1.kind, combined_constraints);
                    substitutions.insert(v2.clone(), Ty::TypeVar(id));
                } else {
                    let id = TypeVarID::new(v2.id, v2.kind, combined_constraints);
                    substitutions.insert(v1.clone(), Ty::TypeVar(id));
                }
                Self::normalize_substitutions(substitutions);
                Ok(())
            }

            (Ty::TypeVar(v), ty) | (ty, Ty::TypeVar(v)) => {
                if Self::occurs_check(&v, &ty, substitutions) {
                    Err(TypeError::OccursConflict)
                } else {
                    // Having this here is icky.
                    if !v.constraints.is_empty() {
                        let checker = SatisfiesChecker::new(self.env, &ty, &v.constraints);
                        let unifications = checker.check()?;
                        for (lhs, rhs) in unifications {
                            self.unify(&lhs, &rhs, substitutions)?;
                        }
                    }

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
                    log::trace!("Member substitution: {type_param:?} -> {type_arg:?}");
                    member_substitutions.insert(type_param.type_var.clone(), type_arg.clone());
                }
                let specialized_ty = Self::substitute_ty_with_map(
                    &Ty::EnumVariant(enum_id, func_args),
                    substitutions,
                );

                self.unify(&ret, &specialized_ty, substitutions)?;

                // Inference treats all callees as funcs, even if it's an enum constructor.
                // for (func_arg, variant_arg) in func_args.iter().zip(variant_args) {
                //     self.unify(func_arg, &variant_arg, substitutions)?;
                // }

                Self::normalize_substitutions(substitutions);

                Ok(())
            }
            _ => {
                log::error!(
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

        log::debug!(
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
                    log::error!("occur check failed: {ty:?}");
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
            Ty::Void | Ty::Pointer | Ty::Int | Ty::Float | Ty::Bool => ty.clone(),
        }
    }
}
