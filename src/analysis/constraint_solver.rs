use std::collections::HashMap;

use crate::{
    SourceFile, SymbolID, SymbolTable, Typed, environment::TypeDef, parser::ExprID,
    type_checker::TypeError,
};

use super::{
    environment::EnumVariant,
    type_checker::{Ty, TypeVarID},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    Equality(ExprID, Ty, Ty),
    MemberAccess(ExprID, Ty, String, Ty), // receiver_ty, member_name, result_ty
    UnqualifiedMember(ExprID, String, Ty), // member name, expected type
}

pub struct ConstraintSolver<'a> {
    source_file: &'a mut SourceFile<Typed>,
    symbol_table: &'a SymbolTable,
    constraints: Vec<Constraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(source_file: &'a mut SourceFile<Typed>, symbol_table: &'a mut SymbolTable) -> Self {
        Self {
            constraints: source_file.constraints().clone(),
            source_file,
            symbol_table,
        }
    }

    pub fn solve(&mut self) -> Result<(), TypeError> {
        let mut substitutions = HashMap::<TypeVarID, Ty>::new();
        log::info!("solving {:#?}", self.constraints);

        while let Some(constraint) = self.constraints.pop() {
            self.solve_constraint(constraint, &mut substitutions)?
        }

        for typed_expr in &mut self.source_file.types_mut().values_mut() {
            typed_expr.ty = Self::apply(&typed_expr.ty, &substitutions, 0);
        }

        Ok(())
    }

    fn solve_constraint(
        &mut self,
        constraint: Constraint,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), TypeError> {
        match constraint {
            Constraint::Equality(node_id, lhs, rhs) => {
                let lhs = Self::apply(&lhs, substitutions, 0);
                let rhs = Self::apply(&rhs, substitutions, 0);

                Self::unify(&lhs, &rhs, substitutions).map_err(|err| {
                    log::error!("{err:?}");
                    err
                })?;

                self.source_file.define(node_id, lhs);
            }
            Constraint::UnqualifiedMember(node_id, member_name, result_ty) => {
                let result_ty = Self::apply(&result_ty, substitutions, 0);

                // Look for matching constructors based on the result_ty
                match &result_ty {
                    Ty::Func(_arg_tys, ret_ty) => {
                        // This is a constructor call like .some(123)
                        // Look for enum constructors named member_name that take arg_tys and return
                        // something compatible with ret_ty
                        if let Ty::Enum(enum_id, ret_generics) = ret_ty.as_ref() {
                            // Look up the enum and find the variant
                            if let Some(_enum_info) = self
                                .source_file
                                .type_from_symbol(enum_id, self.symbol_table)
                                && let Some(variant_info) = self.find_variant(enum_id, &member_name)
                            {
                                // Create the constructor type for this variant
                                let constructor_ty = self.create_variant_constructor_type(
                                    enum_id,
                                    ret_generics, // We'll create fresh generics
                                    &variant_info,
                                    substitutions,
                                );

                                // Unify the constructor type with result_ty
                                Self::unify(&constructor_ty, &result_ty, substitutions)?;
                                Self::normalize_substitutions(substitutions);

                                self.source_file.register_direct_callable(
                                    node_id,
                                    variant_info.constructor_symbol,
                                );

                                self.source_file.define(node_id, constructor_ty);
                            }
                        }
                    }
                    Ty::Enum(enum_id, _) => {
                        // This is a valueless constructor like .none
                        if let Some(_enum_info) = self
                            .source_file
                            .type_from_symbol(enum_id, self.symbol_table)
                            && let Some(variant_info) = self.find_variant(enum_id, &member_name)
                            && variant_info.values.is_empty()
                        {
                            // This is a valueless variant, unify with the enum type directly
                            self.source_file.define(node_id, result_ty.clone());
                        }
                    }
                    _ => {
                        // Unknown result type, leave as type variable for now
                    }
                }
            }
            Constraint::MemberAccess(node_id, receiver_ty, member_name, result_ty) => {
                let receiver_ty = Self::apply(&receiver_ty, substitutions, 0);
                let result_ty = Self::apply(&result_ty, substitutions, 0);

                log::debug!("solving MemberAccess constraint");

                match &receiver_ty {
                    Ty::Enum(enum_id, generics) => {
                        // Look up the enum definition
                        if let Some(enum_info) = self
                            .source_file
                            .type_from_symbol(enum_id, self.symbol_table)
                        {
                            // Check if this is a variant constructor
                            log::debug!("Enum info: {enum_info:?}");
                            if let Some(variant_info) = self.find_variant(enum_id, &member_name) {
                                // Create the constructor type
                                log::debug!("Variant info: {variant_info:?}");

                                let variant_ty = self.create_variant_constructor_type(
                                    enum_id,
                                    generics,
                                    &variant_info,
                                    substitutions,
                                );

                                // Unify with the result type
                                Self::unify(&variant_ty, &result_ty, substitutions)?;
                                Self::normalize_substitutions(substitutions);
                                self.source_file.define(node_id, variant_ty);
                            } else {
                                log::debug!("Could not find variant named {member_name:?}");
                            }
                            // Future: Check for methods, fields, etc.
                        } else {
                            log::debug!("Could not find type from symbol: {enum_id:?}");
                        }
                    }
                    // Future: Handle other receiver types (structs, etc.)
                    _ => {
                        log::debug!(
                            "For now just unify with the result type: {node_id:?}, {result_ty:?}"
                        );
                        // For now, just unify with the result type
                        self.source_file.define(node_id, result_ty);
                    }
                }
            }
        };

        Ok(())
    }

    fn create_variant_constructor_type(
        &mut self,
        enum_id: &SymbolID,
        // `instance_generics` are the type arguments for this specific instance of the enum,
        // so like for Option<Int>, this would be [TypeVar(that_will_become_Int)].
        // These are ALREADY FRESHLY INSTANTIATED from the enum's scheme by the caller (TypeChecker).
        instance_generics: &[Ty],
        variant_info: &EnumVariant, // variant_info.values refers to original enum type params (e.g. T from Option<T>)
        substitutions: &mut HashMap<TypeVarID, Ty>, // Global substitutions being built by the solver
    ) -> Ty {
        // These formal parameters are the Ty::TypeVar created during `hoist_enums`.
        let enum_def = match self.source_file.type_def(enum_id) {
            Some(TypeDef::Enum(ed)) => ed,
            _ => panic!("EnumDef not found for {enum_id:?} during variant constructor creation"),
        };

        let mut local_param_to_arg_subst = HashMap::new();
        for (formal_param_ty, actual_instance_arg_ty) in enum_def
            .type_parameters
            .iter()
            .zip(instance_generics.iter())
        {
            if let Ty::TypeVar(formal_param_id) = formal_param_ty {
                // `actual_instance_arg_ty` is the specific type (often a fresh TypeVar) for this instance.
                local_param_to_arg_subst
                    .insert(formal_param_id.clone(), actual_instance_arg_ty.clone());
            } else {
                // This indicates an issue with how EnumDef.type_parameters were stored, they should be TypeVars.
                log::error!(
                    "Formal type parameter in EnumDef was not a TypeVar: {formal_param_ty:?}"
                );
            }
        }

        // Instantiate the variant's value types (constructor arguments) using this local substitution first,
        // then apply the global substitutions.
        let constructor_arg_tys: Vec<Ty> = variant_info
            .values
            .iter()
            .map(|formal_val_ty| {
                let local_subst = Self::apply(formal_val_ty, &local_param_to_arg_subst, 0);
                Self::apply(&local_subst, substitutions, 0)
            })
            .map(|instantiated_val_ty| {
                // Step 3b: Apply global solver substitutions
                Self::apply(&instantiated_val_ty, substitutions, 0)
            })
            .collect();

        // The return type of the constructor is the enum type itself, with its actual instance generics.
        let constructor_return_ty = Ty::Enum(
            *enum_id,
            instance_generics
                .iter()
                .map(|g_ty| Self::apply(g_ty, substitutions, 0))
                .collect(),
        );

        if variant_info.values.is_empty() {
            // If no values, it's not a function, it's just the enum type itself (fully substituted).
            constructor_return_ty
        } else {
            Ty::Func(constructor_arg_tys, Box::new(constructor_return_ty))
        }
    }

    fn find_variant(&mut self, enum_id: &SymbolID, name: &String) -> Option<EnumVariant> {
        let Some(TypeDef::Enum(enum_def)) = self.source_file.type_def(enum_id) else {
            return None;
        };
        log::debug!("Variants: {:?}", enum_def.variants);
        for variant in enum_def.variants.iter() {
            log::debug!("Checking variant: {variant:?}");
            if variant.name == *name {
                return Some(variant.clone());
            }
        }
        None
    }

    fn apply(ty: &Ty, substitutions: &HashMap<TypeVarID, Ty>, depth: u32) -> Ty {
        if depth > 100 {
            return ty.clone();
        }

        match ty {
            Ty::Int => ty.clone(),
            Ty::Float => ty.clone(),
            Ty::Bool => ty.clone(),
            Ty::Func(params, returning) => {
                let applied_params = params
                    .iter()
                    .map(|param| Self::apply(param, substitutions, depth + 1).clone())
                    .collect();

                let applied_return = Self::apply(returning, substitutions, depth + 1);

                Ty::Func(applied_params, Box::new(applied_return))
            }
            Ty::TypeVar(type_var) => {
                if let Some(ty) = substitutions.get(type_var) {
                    Self::apply(ty, substitutions, depth + 1)
                } else {
                    ty.clone()
                }
            }
            Ty::Enum(name, generics) => {
                let applied_generics = generics
                    .iter()
                    .map(|generic| Self::apply(generic, substitutions, depth + 1))
                    .collect();
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
                let captures = captures
                    .iter()
                    .map(|c| Self::apply(c, substitutions, depth + 1))
                    .collect();
                Ty::Closure { func, captures }
            }
            Ty::Array(ty) => Ty::Array(Self::apply(ty, substitutions, depth + 1).into()),
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
        lhs: &Ty,
        rhs: &Ty,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), TypeError> {
        log::trace!("Unifying: {lhs:?} and {rhs:?}");

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
                    Ok(())
                }
            }
            (Ty::Func(lhs_params, lhs_returning), Ty::Func(rhs_params, rhs_returning))
                if lhs_params.len() == rhs_params.len() =>
            {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    Self::unify(lhs, &rhs, substitutions)?;
                }

                Self::unify(&lhs_returning, &rhs_returning, substitutions)?;
                Self::normalize_substitutions(substitutions);

                Ok(())
            }
            (Ty::Closure { func: lhs_func, .. }, Ty::Closure { func: rhs_func, .. }) => {
                Self::unify(&lhs_func, &rhs_func, substitutions)?;
                Ok(())
            }
            (func, Ty::Closure { func: closure, .. })
            | (Ty::Closure { func: closure, .. }, func)
                if matches!(func, Ty::Func(_, _)) =>
            {
                Self::unify(&func, &closure, substitutions)?;
                Ok(())
            }
            (Ty::Enum(_, lhs_types), Ty::Enum(_, rhs_types))
                if lhs_types.len() == rhs_types.len() =>
            {
                for (lhs, rhs) in lhs_types.iter().zip(rhs_types) {
                    Self::unify(lhs, &rhs, substitutions)?;
                    Self::normalize_substitutions(substitutions);
                }

                Ok(())
            }
            _ => Err(TypeError::Mismatch(
                Self::apply(lhs, substitutions, 0),
                Self::apply(rhs, substitutions, 0),
            )),
        }
    }

    /// Returns true if `v` occurs inside `ty`
    fn occurs_check(v: &TypeVarID, ty: &Ty, substitutions: &HashMap<TypeVarID, Ty>) -> bool {
        let ty = Self::apply(ty, substitutions, 0);
        match &ty {
            Ty::TypeVar(tv) => tv == v,
            Ty::Func(params, returning) => {
                // check each parameter and the return type
                let oh = params
                    .iter()
                    .any(|param| Self::occurs_check(v, param, substitutions))
                    || Self::occurs_check(v, returning, substitutions);

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
}
