use std::collections::HashMap;

use crate::{SourceFile, SymbolID, Typed, parser::ExprID};

use super::{
    environment::{EnumVariant, TypeDef},
    type_checker::{Ty, TypeDefs, TypeVarID},
};

#[derive(Debug)]
pub enum ConstraintError {
    TypeConflict(Ty, Ty),
    OccursConflict,
}

#[derive(Debug, Clone)]
pub enum ConstrainedExpr {
    Ty(Ty),
    TypeScheme(Ty, Vec<TypeVarID>),
}

#[derive(Debug, Clone)]
pub enum Constraint {
    Equality(ExprID, Ty, Ty),
    MemberAccess(ExprID, Ty, String, Ty), // receiver_ty, member_name, result_ty
}

pub struct ConstraintSolver<'a> {
    source_file: &'a mut SourceFile<Typed>,
    types: TypeDefs,
    constraints: Vec<Constraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(
        source_file: &'a mut SourceFile<Typed>,
        constraints: Vec<Constraint>,
        types: TypeDefs,
    ) -> Self {
        Self {
            source_file,
            constraints,
            types,
        }
    }

    pub fn solve(&mut self) -> Result<(), ConstraintError> {
        let mut substitutions = HashMap::<TypeVarID, Ty>::new();
        log::info!("solving {:#?}", self.constraints);

        while let Some(constraint) = self.constraints.pop() {
            self.solve_constraint(constraint, &mut substitutions)?
        }

        for typed_expr in &mut self.source_file.types_mut().values_mut() {
            typed_expr.ty = Self::apply(typed_expr.ty.clone(), &substitutions);
        }

        Ok(())
    }

    fn solve_constraint(
        &mut self,
        constraint: Constraint,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), ConstraintError> {
        match constraint {
            Constraint::Equality(node_id, lhs, rhs) => {
                let lhs = Self::apply(lhs, substitutions);
                let rhs = Self::apply(rhs, substitutions);

                Self::unify(&lhs, &rhs, substitutions).map_err(|err| {
                    log::error!("{:?}", err);
                    err
                })?;

                self.source_file.define(node_id, lhs);
            }
            Constraint::MemberAccess(node_id, receiver_ty, member_name, result_ty) => {
                let receiver_ty = Self::apply(receiver_ty, substitutions);
                let result_ty = Self::apply(result_ty, substitutions);

                log::debug!("solving MemberAccess constraint");

                match &receiver_ty {
                    Ty::Enum(enum_id, generics) => {
                        // Look up the enum definition
                        if let Some(enum_info) = self.source_file.type_from_symbol(enum_id) {
                            // Check if this is a variant constructor
                            log::debug!("Enum info: {:?}", enum_info);
                            if let Some(variant_info) = self.find_variant(enum_id, &member_name) {
                                // Create the constructor type
                                log::debug!("Variant info: {:?}", variant_info);

                                let variant_ty = self.create_variant_constructor_type(
                                    &enum_id,
                                    generics,
                                    &variant_info,
                                    substitutions,
                                );

                                // Unify with the result type
                                Self::unify(&variant_ty, &result_ty, substitutions)?;
                                self.source_file.define(node_id, variant_ty);
                            } else {
                                log::debug!("Could not find variant named {:?}", member_name);
                            }
                            // Future: Check for methods, fields, etc.
                        } else {
                            log::debug!("Could not find type from symbol: {:?}", enum_id);
                        }
                    }
                    // Future: Handle other receiver types (structs, etc.)
                    _ => {
                        log::debug!(
                            "For now just unify with the result type: {:?}, {:?}",
                            node_id,
                            result_ty
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
        // e.g., for Option<Int>, this would be [TypeVar(that_will_become_Int)].
        // These are ALREADY FRESHLY INSTANTIATED from the enum's scheme by the caller (TypeChecker).
        instance_generics: &[Ty],
        variant_info: &EnumVariant, // variant_info.values refers to original enum type params (e.g. T from Option<T>)
        substitutions: &mut HashMap<TypeVarID, Ty>, // Global substitutions being built by the solver
    ) -> Ty {
        // 1. Get the EnumDef to find its declared (formal) type parameters.
        // These formal parameters are the Ty::TypeVar created during `hoist_enums`.
        let enum_def = match self.types.get(enum_id) {
            Some(TypeDef::Enum(ed)) => ed,
            _ => panic!(
                "EnumDef not found for {:?} during variant constructor creation",
                enum_id
            ),
        };

        // 2. Create a local substitution map: formal enum type param ID -> actual instance generic arg type.
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
                    "Formal type parameter in EnumDef was not a TypeVar: {:?}",
                    formal_param_ty
                );
            }
        }

        // 3. Instantiate the variant's value types (constructor arguments) using this local substitution first,
        //    then apply the global substitutions.
        let constructor_arg_tys: Vec<Ty> = variant_info
            .values
            .iter()
            .map(|formal_val_ty| {
                // Step 3a: Apply local substitution (formal param -> instance arg)
                Self::apply(formal_val_ty.clone(), &local_param_to_arg_subst)
            })
            .map(|instantiated_val_ty| {
                // Step 3b: Apply global solver substitutions
                Self::apply(instantiated_val_ty, substitutions)
            })
            .collect();

        // 4. The return type of the constructor is the enum type itself, with its actual instance generics.
        // These instance_generics should also be fully resolved using global substitutions.
        let constructor_return_ty = Ty::Enum(
            enum_id.clone(),
            instance_generics
                .iter()
                .map(|g_ty| Self::apply(g_ty.clone(), substitutions))
                .collect(),
        );

        if variant_info.values.is_empty() {
            // If no values, it's not a function, it's just the enum type itself (fully substituted).
            constructor_return_ty
        } else {
            Ty::Func(constructor_arg_tys, Box::new(constructor_return_ty))
        }
    }

    fn find_variant(&self, enum_id: &SymbolID, name: &String) -> Option<EnumVariant> {
        let Some(TypeDef::Enum(enum_def)) = self.types.get(enum_id) else {
            return None;
        };
        log::debug!("Variants: {:?}", enum_def.variants);
        for variant in enum_def.variants.iter() {
            log::debug!("Checking variant: {:?}", variant);
            if variant.name == *name {
                return Some(variant.clone());
            }
        }
        None
    }

    fn apply(ty: Ty, substitutions: &HashMap<TypeVarID, Ty>) -> Ty {
        match ty {
            Ty::Int => ty,
            Ty::Float => ty,
            Ty::Bool => ty,
            Ty::Func(params, returning) => {
                let applied_params = params
                    .iter()
                    .map(|param| Self::apply(param.clone(), substitutions))
                    .collect();

                let applied_return = Self::apply(*returning, substitutions);

                Ty::Func(applied_params, Box::new(applied_return))
            }
            Ty::TypeVar(ref type_var) => {
                if let Some(ty) = substitutions.get(type_var) {
                    Self::apply(ty.clone(), substitutions)
                } else {
                    ty
                }
            }
            Ty::Enum(name, generics) => {
                let applied_generics = generics
                    .iter()
                    .map(|generic| Self::apply(generic.clone(), substitutions))
                    .collect();
                Ty::Enum(name, applied_generics)
            }
            Ty::EnumVariant(enum_id, values) => {
                let applied_values = values
                    .iter()
                    .map(|variant| Self::apply(variant.clone(), substitutions))
                    .collect();
                Ty::EnumVariant(enum_id, applied_values)
            }
            Ty::Void => ty,
        }
    }

    fn unify(
        lhs: &Ty,
        rhs: &Ty,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), ConstraintError> {
        log::trace!("Unifying: {:?} and {:?}", lhs, rhs);

        match (lhs, rhs) {
            // They're the same, sick.
            (a, b) if a == b => Ok(()),
            (Ty::TypeVar(v), ty) | (ty, Ty::TypeVar(v)) => {
                if Self::occurs_check(v, ty, substitutions) {
                    Err(ConstraintError::OccursConflict)
                } else {
                    substitutions.insert(v.clone(), ty.clone());
                    Ok(())
                }
            }
            (Ty::Func(lhs_params, lhs_returning), Ty::Func(rhs_params, rhs_returning))
                if lhs_params.len() == rhs_params.len() =>
            {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    Self::unify(lhs, rhs, substitutions)?;
                }

                Self::unify(lhs_returning, rhs_returning, substitutions)?;

                Ok(())
            }
            (Ty::Enum(_, lhs_types), Ty::Enum(_, rhs_types))
                if lhs_types.len() == rhs_types.len() =>
            {
                for (lhs, rhs) in lhs_types.iter().zip(rhs_types) {
                    Self::unify(lhs, rhs, substitutions)?;
                }

                Ok(())
            }
            _ => panic!("Type mismatch {:#?} / {:#?}", lhs, rhs),
        }
    }

    /// Returns true if `v` occurs inside `ty` (after applying current `subs`).
    fn occurs_check(v: &TypeVarID, ty: &Ty, substitutions: &HashMap<TypeVarID, Ty>) -> bool {
        let ty = Self::apply(ty.clone(), substitutions);
        match &ty {
            Ty::TypeVar(tv) => tv == v,
            Ty::Func(params, returning) => {
                // check each parameter and the return type
                let oh = params
                    .iter()
                    .any(|param| Self::occurs_check(v, param, substitutions))
                    || Self::occurs_check(v, returning, substitutions);

                if oh {
                    log::error!("occur check failed: {:?}", ty);
                }

                oh
            }
            _ => false,
        }
    }
}
