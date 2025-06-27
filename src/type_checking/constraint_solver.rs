use std::collections::HashMap;

use crate::{
    NameResolved, Phase, SourceFile, SymbolID, SymbolTable,
    diagnostic::Diagnostic,
    environment::Environment,
    expr::Expr,
    name::Name,
    parser::ExprID,
    ty::Ty,
    type_checker::{Scheme, TypeError, TypeVarKind},
};

use super::type_checker::TypeVarID;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    Equality(ExprID, Ty, Ty),
    MemberAccess(ExprID, Ty, String, Ty), // receiver_ty, member_name, result_ty
    UnqualifiedMember(ExprID, String, Ty), // member name, expected type
    InitializerCall {
        expr_id: ExprID,
        initializes_id: SymbolID,
        args: Vec<Ty>,
        ret: Ty,
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
                ret,
            } => Constraint::InitializerCall {
                expr_id: *expr_id,
                initializes_id: *initializes_id,
                args: args
                    .iter()
                    .map(|a| ConstraintSolver::<NameResolved>::apply(a, substitutions, 0))
                    .collect(),
                ret: ret.clone(),
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
        }
    }
}

pub struct ConstraintSolver<'a, P: Phase = NameResolved> {
    source_file: &'a mut SourceFile<P>,
    env: &'a mut Environment,
    symbol_table: &'a mut SymbolTable,
    constraints: Vec<Constraint>,
}

impl<'a, P: Phase> ConstraintSolver<'a, P> {
    pub fn new(
        source_file: &'a mut SourceFile<P>,
        env: &'a mut Environment,
        symbol_table: &'a mut SymbolTable,
    ) -> Self {
        Self {
            constraints: env.constraints().clone(),
            env,
            source_file,
            symbol_table,
        }
    }

    pub fn solve(&mut self) -> HashMap<TypeVarID, Ty> {
        let mut substitutions = HashMap::<TypeVarID, Ty>::new();

        while let Some(constraint) = self.constraints.pop() {
            match self.solve_constraint(&constraint, &mut substitutions) {
                Ok(_) => (),
                Err(err) => {
                    self.source_file
                        .diagnostics
                        .insert(Diagnostic::typing(*constraint.expr_id(), err));
                }
            }
        }

        for (_id, typed_expr) in &mut self.env.typed_exprs.iter_mut() {
            typed_expr.ty = Self::apply(&typed_expr.ty, &substitutions, 0);

            // Try to fill in the symbol ID of types of variables
            let this_symbol = match typed_expr.expr {
                Expr::Variable(Name::Resolved(symbol_id, _), _) => symbol_id,
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

            symbol_info
                .definition
                .as_mut()
                .map(|d| d.sym = Some(def_symbol));
        }

        self.constraints.clear();

        substitutions
    }

    fn solve_constraint(
        &mut self,
        constraint: &Constraint,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), TypeError> {
        log::info!("Solving constraint: {:?}", constraint);
        match &constraint {
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
                        Ty::TypeVar(self.env.new_type_variable(TypeVarKind::Unbound)),
                    );
                }
                let instantiated_ty = Self::substitute_ty_with_map(&ty, &mapping);

                self.unify(&ty, &instantiated_ty, substitutions)?;
                Self::normalize_substitutions(substitutions);
            }
            Constraint::UnqualifiedMember(_node_id, member_name, result_ty) => {
                log::warn!("Unqualified member constraint: {:?}", constraint)
            }
            Constraint::MemberAccess(_node_id, receiver_ty, member_name, result_ty) => {
                let receiver_ty = Self::apply(receiver_ty, substitutions, 0);
                let result_ty = Self::apply(result_ty, substitutions, 0);

                let (member_ty, type_params, type_args) = match &receiver_ty {
                    Ty::Struct(struct_id, generics) => {
                        let struct_def = self.env.lookup_struct(&struct_id).unwrap();
                        let member_ty = struct_def.member_ty(&member_name).unwrap();

                        log::warn!(
                            "MemberAccess {receiver_ty:?}.{member_name:?} {:?} -> {:?} {:?}",
                            member_ty,
                            result_ty,
                            generics
                        );

                        (
                            member_ty.clone(),
                            struct_def.type_parameters.clone(),
                            generics,
                        )
                    }
                    Ty::Enum(enum_id, generics) => {
                        let enum_def = self.env.lookup_enum(&enum_id).unwrap();

                        let Some(member_ty) = enum_def.member_ty(&member_name) else {
                            return Err(TypeError::Unknown(format!(
                                "Member not found for enum {}: {}",
                                enum_def.name_str, member_name
                            )));
                        };

                        log::warn!(
                            "MemberAccess {receiver_ty:?}.{member_name:?} {:?} -> {:?} {:?}",
                            member_ty,
                            result_ty,
                            generics
                        );

                        (
                            member_ty.clone(),
                            enum_def.type_parameters.clone(),
                            generics,
                        )
                    }
                    _ => {
                        todo!("{:?} {:?}", receiver_ty, result_ty);
                        // self.constraints.push(constraint.clone());
                    }
                };

                let mut member_substitutions = substitutions.clone();
                for (type_param, type_arg) in type_params.iter().zip(type_args) {
                    if let Ty::TypeVar(type_var) = type_param {
                        log::trace!("Member substitution: {:?} -> {:?}", type_var, type_arg);
                        member_substitutions.insert(type_var.clone(), type_arg.clone());
                    }
                }

                let specialized_ty =
                    Self::substitute_ty_with_map(&member_ty, &member_substitutions);
                self.unify(&result_ty, &specialized_ty, substitutions)?;
                Self::normalize_substitutions(substitutions);
            }
            Constraint::InitializerCall {
                initializes_id,
                args,
                ret,
                ..
            } => {
                let Some(struct_def) = self.env.lookup_struct(initializes_id) else {
                    return Err(TypeError::Unresolved(
                        "did not find struct def for initialization".into(),
                    ));
                };

                // TODO: Support multiple initializers
                let initializer = &struct_def.initializers[0];
                let Ty::Init(_, params, _) = &initializer.ty else {
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

                self.unify(&Ty::Struct(*initializes_id, vec![]), ret, substitutions)?;
                Self::normalize_substitutions(substitutions);
            }
            Constraint::VariantMatch {
                scrutinee_ty,
                variant_name,
                field_tys,
                ..
            } => {
                let Ty::Enum(enum_id, _) = Self::apply(scrutinee_ty, &substitutions, 0) else {
                    panic!()
                };

                let Some(enum_def) = self.env.lookup_enum(&enum_id) else {
                    panic!()
                };

                let Some(variant) = enum_def.variants.iter().find(|v| v.name == *variant_name)
                else {
                    panic!()
                };

                let Ty::EnumVariant(_, values) = &variant.ty else {
                    unreachable!();
                };

                for (value, field) in values.iter().zip(field_tys) {
                    self.unify(value, field, substitutions)?;
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
            Ty::Init(struct_id, params, generics) => Ty::Init(
                *struct_id,
                Self::apply_multiple(&params, substitutions, depth + 1),
                Self::apply_multiple(generics, substitutions, depth + 1),
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

    fn unify(
        &self,
        lhs: &Ty,
        rhs: &Ty,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), TypeError> {
        log::trace!("Unifying: {lhs:?} <> {rhs:?}");

        match (
            Self::apply(lhs, substitutions, 0),
            Self::apply(rhs, substitutions, 0),
        ) {
            // They're the same, sick.
            (a, b) if a == b => Ok(()),

            (Ty::TypeVar(v1), Ty::TypeVar(v2)) => {
                // When unifying two type variables, pick one consistently
                if v1.0 < v2.0 {
                    substitutions.insert(v2.clone(), Ty::TypeVar(v1.clone()));
                } else {
                    substitutions.insert(v1.clone(), Ty::TypeVar(v2.clone()));
                }
                Self::normalize_substitutions(substitutions);
                Ok(())
            }

            (Ty::TypeVar(v), ty) | (ty, Ty::TypeVar(v)) => {
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

                if let (Ty::TypeVar(ret_var), concrete_ret) =
                    (lhs_returning.as_ref(), rhs_returning.as_ref())
                {
                    // If we're unifying a function with a TypeVar return against a function with a concrete return,
                    // record that the TypeVar should be the concrete type
                    if !matches!(concrete_ret, Ty::TypeVar(_)) {
                        substitutions.insert(ret_var.clone(), concrete_ret.clone());
                    }
                }

                if let (concrete_ret, Ty::TypeVar(ret_var)) =
                    (lhs_returning.as_ref(), rhs_returning.as_ref())
                    && !matches!(concrete_ret, Ty::TypeVar(_))
                {
                    substitutions.insert(ret_var.clone(), concrete_ret.clone());
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
                    if let Ty::TypeVar(type_var) = type_param {
                        log::trace!("Member substitution: {:?} -> {:?}", type_var, type_arg);
                        member_substitutions.insert(type_var.clone(), type_arg.clone());
                    }
                }
                let specialized_ty =
                    Self::substitute_ty_with_map(&Ty::Enum(enum_id, func_args), substitutions);

                self.unify(&ret, &specialized_ty, substitutions)?;

                // Inference treats all callees as funcs, even if it's an enum constructor.
                // for (func_arg, variant_arg) in func_args.iter().zip(variant_args) {
                //     self.unify(func_arg, &variant_arg, substitutions)?;
                // }

                Self::normalize_substitutions(substitutions);

                Ok(())
            }
            _ => {
                log::error!("Mismatch: {lhs:?} and {rhs:?}");
                Err(TypeError::Mismatch(
                    Self::apply(lhs, substitutions, 0),
                    Self::apply(rhs, substitutions, 0),
                ))
            }
        }
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
                    // Important: Clone the substituted type. If it's also a TypeVar that needs further substitution,
                    // the caller (or a broader substitution application like `apply_substitutions_to_ty`) must handle it.
                    // This function only applies one layer from the provided map.
                    substituted_ty.clone()
                } else {
                    ty.clone() // Not in this substitution map, return as is.
                }
            }
            Ty::Init(struct_id, params, generics) => {
                let applied_params = params
                    .iter()
                    .map(|param| Self::substitute_ty_with_map(param, substitutions))
                    .collect();
                let applied_generics = generics
                    .iter()
                    .map(|g| Self::substitute_ty_with_map(g, substitutions))
                    .collect();
                Ty::Init(*struct_id, applied_params, applied_generics)
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
            Ty::Void | Ty::Pointer | Ty::Int | Ty::Float | Ty::Bool => ty.clone(),
        }
    }
}
