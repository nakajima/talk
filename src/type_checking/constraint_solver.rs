use std::collections::HashMap;

use crate::{
    Phase, SourceFile, SymbolID, SymbolTable, Typed,
    diagnostic::Diagnostic,
    environment::{Environment, TypeDef},
    expr::Expr,
    name::Name,
    parser::ExprID,
    ty::Ty,
    type_checker::{TypeError, TypeVarKind},
};

use super::{environment::EnumVariant, type_checker::TypeVarID};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    Equality(ExprID, Ty, Ty),
    MemberAccess(ExprID, Ty, String, Ty), // receiver_ty, member_name, result_ty
    UnqualifiedMember(ExprID, String, Ty), // member name, expected type
    InitializerCall {
        expr_id: ExprID,
        initializes_id: SymbolID,
        args: Vec<Ty>,
        ret: TypeVarID,
    },
    VariantMatch {
        scrutinee_ty: Ty, // The type of the value being matched (the `expected` type)
        variant_name: String,
        // The list of fresh TypeVars created for each field in the pattern.
        field_tys: Vec<Ty>,
    },
    InstanceOf {
        expr_id: ExprID,
        ty: Ty,
        symbol_id: SymbolID,
    },
    GenericApplication {
        // A placeholder for the generic type being applied (e.g., Array)
        generic_ty: Ty,
        // A list of placeholders for the arguments (e.g., [Int])
        arg_tys: Vec<Ty>,
        // A new placeholder for the final, specialized type (e.g., Array<Int>)
        result_ty: Ty,
    },
}

impl Constraint {
    fn expr_id(&self) -> &ExprID {
        match self {
            Self::Equality(id, _, _) => id,
            Self::MemberAccess(id, _, _, _) => id,
            Self::UnqualifiedMember(id, _, _) => id,
            Self::InitializerCall { .. } => todo!(),
            Self::VariantMatch { .. } => todo!(),
            Self::InstanceOf { expr_id, .. } => expr_id,
            Self::GenericApplication { .. } => todo!(),
        }
    }
}

pub struct ConstraintSolver<'a, P: Phase> {
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

        substitutions
    }

    fn solve_constraint(
        &mut self,
        constraint: &Constraint,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), TypeError> {
        log::info!("Solving constraint: {:?}", constraint);
        match &constraint {
            Constraint::Equality(node_id, lhs, rhs) => {
                let lhs = Self::apply(lhs, substitutions, 0);
                let rhs = Self::apply(rhs, substitutions, 0);

                Self::unify(&lhs, &rhs, substitutions).map_err(|err| {
                    log::error!("{err:?}");
                    err
                })?;

                Self::normalize_substitutions(substitutions);
            }
            Constraint::GenericApplication { .. } => todo!(),
            Constraint::InstanceOf { ty, symbol_id, .. } => {
                let scheme = self.env.lookup_symbol(symbol_id)?.clone();
                let ty = scheme.ty;

                // 1. Instantiate the scheme
                let mut mapping = HashMap::new();
                for unbound_var in &scheme.unbound_vars {
                    mapping.insert(
                        unbound_var.clone(),
                        Ty::TypeVar(self.env.new_type_variable(TypeVarKind::Unbound)),
                    );
                }
                let instantiated_ty = Self::substitute_ty_with_map(&ty, &mapping);

                // 2. Unify with the placeholder
                Self::unify(&ty, &instantiated_ty, substitutions)?;
                Self::normalize_substitutions(substitutions);
            }
            Constraint::UnqualifiedMember(node_id, member_name, result_ty) => {
                // let result_ty = Self::apply(result_ty, substitutions, 0);

                // // Look for matching constructors based on the result_ty
                // match &result_ty {
                //     Ty::Func(_arg_tys, ret_ty, _generics) => {
                //         // This is a constructor call like .some(123)
                //         // Look for enum constructors named member_name that take arg_tys and return
                //         // something compatible with ret_ty
                //         if let Ty::Enum(enum_id, ret_generics) = ret_ty.as_ref() {
                //             // Look up the enum and find the variant
                //             if let Some(variant_info) = self.find_variant(enum_id, member_name) {
                //                 // Create the constructor type for this variant
                //                 let constructor_ty = self.create_variant_constructor_type(
                //                     enum_id,
                //                     ret_generics, // We'll create fresh generics
                //                     &variant_info,
                //                     substitutions,
                //                 );

                //                 // Unify the constructor type with result_ty
                //                 Self::unify(&constructor_ty, &result_ty, substitutions)?;
                //                 Self::normalize_substitutions(substitutions);

                //                 // self.source_file.register_direct_callable(
                //                 //     *node_id,
                //                 //     variant_info.constructor_symbol,
                //                 // );

                //                 self.source_file.define(*node_id, constructor_ty, self.env);
                //             }
                //         }
                //     }
                //     Ty::Enum(enum_id, _) => {
                //         // This is a valueless constructor like .none
                //         if let Some(variant_info) = self.find_variant(enum_id, member_name)
                //             && variant_info.values.is_empty()
                //         {
                //             // This is a valueless variant, unify with the enum type directly
                //             self.source_file
                //                 .define(*node_id, result_ty.clone(), self.env);
                //         }
                //     }
                //     _ => {
                //         // Unknown result type, leave as type variable for now
                //     }
                // }
            }
            Constraint::MemberAccess(node_id, receiver_ty, member_name, result_ty) => {
                let receiver_ty = Self::apply(receiver_ty, substitutions, 0);
                let result_ty = Self::apply(result_ty, substitutions, 0);

                // match &receiver_ty {
                //     Ty::Struct(struct_id, generics) => {
                //         let Some(TypeDef::Struct(struct_def)) =
                //             self.env.lookup_type(struct_id).cloned()
                //         else {
                //             log::info!("For now, just unify with the result type");
                //             self.source_file.define(*node_id, result_ty, self.env);
                //             return Ok(());
                //         };

                //         log::info!("receiver_ty: {receiver_ty:?}");

                //         if let Some(method) = struct_def.methods.get(member_name) {
                //             // Create a substitution map from the struct's generic parameters to the concrete types.
                //             let mut substitution_map = HashMap::new();
                //             for (param_ty, arg_ty) in
                //                 struct_def.type_parameters.iter().zip(generics.iter())
                //             {
                //                 if let Ty::TypeVar(param_id) = param_ty {
                //                     substitution_map.insert(param_id.clone(), arg_ty.clone());
                //                 }
                //             }

                //             // Specialize the method's type.
                //             let specialized_method_ty =
                //                 Self::substitute_ty_with_map(method.ty.clone(), &substitution_map);

                //             // IMPORTANT: Do NOT instantiate here - we want to use the same type variables
                //             // that are already in the struct instance's generics
                //             log::info!("specialized_method_ty: {specialized_method_ty:?}");

                //             // Unify with the specialized type directly (no instantiation)
                //             Self::unify(&specialized_method_ty, &result_ty, substitutions)?;

                //             // Apply the substitutions to get the final type
                //             let final_ty = Self::apply(&specialized_method_ty, substitutions, 0);
                //             log::info!("Set type for member access {node_id:?}: {final_ty:?}");
                //             self.source_file.define(*node_id, final_ty, self.env);
                //         }

                //         if let Some(property) = struct_def
                //             .properties
                //             .iter()
                //             .find(|p| &p.name == member_name)
                //         {
                //             // Also specialize property types.
                //             let mut substitution_map = HashMap::new();
                //             for (param_ty, arg_ty) in
                //                 struct_def.type_parameters.iter().zip(generics.iter())
                //             {
                //                 if let Ty::TypeVar(param_id) = param_ty {
                //                     substitution_map.insert(param_id.clone(), arg_ty.clone());
                //                 }
                //             }
                //             let specialized_property_ty = Self::substitute_ty_with_map(
                //                 property.ty.clone(),
                //                 &substitution_map,
                //             );
                //             Self::unify(&specialized_property_ty, &result_ty, substitutions)?;

                //             let final_ty = Self::apply(&specialized_property_ty, substitutions, 0);
                //             self.source_file.define(*node_id, final_ty, self.env);
                //         }
                //     }
                //     Ty::Enum(enum_id, generics) => {
                //         // Look up the enum definition
                //         if let Some(enum_info) = self.env.lookup_enum(enum_id) {
                //             // Check if this is a variant constructor
                //             log::debug!("Enum info: {enum_info:?}");
                //             if let Some(variant_info) = self.find_variant(enum_id, member_name) {
                //                 // Create the constructor type
                //                 log::debug!("Variant info: {variant_info:?}");

                //                 let variant_ty = self.create_variant_constructor_type(
                //                     enum_id,
                //                     generics,
                //                     &variant_info,
                //                     substitutions,
                //                 );

                //                 // Unify with the result type
                //                 Self::unify(&variant_ty, &result_ty, substitutions)?;
                //                 Self::normalize_substitutions(substitutions);
                //                 self.source_file.define(*node_id, variant_ty, self.env);
                //             } else {
                //                 log::error!("Could not find variant named {member_name:?}");
                //             }
                //             // Future: Check for methods, fields, etc.
                //         } else {
                //             panic!("Could not find type from symbol: {enum_id:?}");
                //         }
                //     }
                //     // Future: Handle other receiver types (structs, etc.)
                //     _ => {
                //         log::warn!(
                //             "For now just unify with the result type: {node_id:?}, {result_ty:?}"
                //         );
                //         // For now, just unify with the result type
                //         self.source_file.define(*node_id, result_ty, self.env);
                //     }
                // }
            }
            Constraint::InitializerCall { .. } => todo!(),
            Constraint::VariantMatch { .. } => todo!(),
        };

        Ok(())
    }

    // fn create_variant_constructor_type(
    //     &mut self,
    //     enum_id: &SymbolID,
    //     // `instance_generics` are the type arguments for this specific instance of the enum,
    //     // so like for Option<Int>, this would be [TypeVar(that_will_become_Int)].
    //     // These are ALREADY FRESHLY INSTANTIATED from the enum's scheme by the caller (TypeChecker).
    //     instance_generics: &[Ty],
    //     variant_info: &EnumVariant, // variant_info.values refers to original enum type params (e.g. T from Option<T>)
    //     substitutions: &mut HashMap<TypeVarID, Ty>, // Global substitutions being built by the solver
    // ) -> Ty {
    //     // These formal parameters are the Ty::TypeVar created during `hoist_enums`.
    //     let enum_def = match self.env.lookup_type(enum_id) {
    //         Some(TypeDef::Enum(ed)) => ed,
    //         _ => panic!("EnumDef not found for {enum_id:?} during variant constructor creation"),
    //     };

    //     let mut local_param_to_arg_subst = HashMap::new();
    //     for (formal_param_ty, actual_instance_arg_ty) in enum_def
    //         .type_parameters
    //         .iter()
    //         .zip(instance_generics.iter())
    //     {
    //         if let Ty::TypeVar(formal_param_id) = formal_param_ty {
    //             // `actual_instance_arg_ty` is the specific type (often a fresh TypeVar) for this instance.
    //             local_param_to_arg_subst
    //                 .insert(formal_param_id.clone(), actual_instance_arg_ty.clone());
    //         } else {
    //             // This indicates an issue with how EnumDef.type_parameters were stored, they should be TypeVars.
    //             log::error!(
    //                 "Formal type parameter in EnumDef was not a TypeVar: {formal_param_ty:?}"
    //             );
    //         }
    //     }

    //     // Instantiate the variant's value types (constructor arguments) using this local substitution first,
    //     // then apply the global substitutions.
    //     let constructor_arg_tys: Vec<Ty> = variant_info
    //         .values
    //         .iter()
    //         .map(|formal_val_ty| {
    //             let local_subst = Self::apply(formal_val_ty, &local_param_to_arg_subst, 0);
    //             Self::apply(&local_subst, substitutions, 0)
    //         })
    //         .map(|instantiated_val_ty| {
    //             // Step 3b: Apply global solver substitutions
    //             Self::apply(&instantiated_val_ty, substitutions, 0)
    //         })
    //         .collect();

    //     // The return type of the constructor is the enum type itself, with its actual instance generics.
    //     let constructor_return_ty = Ty::Enum(
    //         *enum_id,
    //         instance_generics
    //             .iter()
    //             .map(|g_ty| Self::apply(g_ty, substitutions, 0))
    //             .collect(),
    //     );

    //     if variant_info.values.is_empty() {
    //         // If no values, it's not a function, it's just the enum type itself (fully substituted).
    //         constructor_return_ty
    //     } else {
    //         Ty::Func(constructor_arg_tys, Box::new(constructor_return_ty), vec![])
    //     }
    // }

    // fn find_variant(&mut self, enum_id: &SymbolID, name: &String) -> Option<EnumVariant> {
    //     let Some(TypeDef::Enum(enum_def)) = self.env.lookup_type(enum_id) else {
    //         return None;
    //     };
    //     log::debug!("Variants: {:?}", enum_def.variants);
    //     for variant in enum_def.variants.iter() {
    //         log::debug!("Checking variant: {variant:?}");
    //         if variant.name == *name {
    //             return Some(variant.clone());
    //         }
    //     }
    //     None
    // }

    fn apply_multiple(types: &[Ty], substitutions: &HashMap<TypeVarID, Ty>, depth: u32) -> Vec<Ty> {
        types
            .iter()
            .map(|ty| Self::apply(ty, substitutions, depth))
            .collect()
    }

    pub fn apply(ty: &Ty, substitutions: &HashMap<TypeVarID, Ty>, depth: u32) -> Ty {
        if depth > 100 {
            return ty.clone();
        }

        match ty {
            Ty::Pointer => ty.clone(),
            Ty::Int => ty.clone(),
            Ty::Float => ty.clone(),
            Ty::Bool => ty.clone(),
            Ty::Func(params, returning, generics) => {
                let applied_params = Self::apply_multiple(params, substitutions, depth);
                let applied_return = Self::apply(returning, substitutions, depth + 1);
                let applied_generics = Self::apply_multiple(generics, substitutions, depth);

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
                let captures = captures
                    .iter()
                    .map(|c| Self::apply(c, substitutions, depth + 1))
                    .collect();
                Ty::Closure { func, captures }
            }
            Ty::Array(ty) => Ty::Array(Self::apply(ty, substitutions, depth + 1).into()),
            Ty::Struct(sym, generics) => Ty::Struct(
                *sym,
                Self::apply_multiple(generics, substitutions, depth + 1),
            ),
            Ty::Init(struct_id, params) => Ty::Init(
                *struct_id,
                params
                    .iter()
                    .map(|p| Self::apply(p, substitutions, depth + 1))
                    .collect(),
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
                    Self::normalize_substitutions(substitutions);
                    Ok(())
                }
            }
            (
                Ty::Func(lhs_params, lhs_returning, lhs_gen),
                Ty::Func(rhs_params, rhs_returning, rhs_gen),
            ) if lhs_params.len() == rhs_params.len() => {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    Self::unify(lhs, &rhs, substitutions)?;
                }

                for (lhs, rhs) in lhs_gen.iter().zip(rhs_gen) {
                    Self::unify(lhs, &rhs, substitutions)?;
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

                Self::unify(&lhs_returning, &rhs_returning, substitutions)?;
                Self::normalize_substitutions(substitutions);

                Ok(())
            }
            (Ty::Closure { func: lhs_func, .. }, Ty::Closure { func: rhs_func, .. }) => {
                Self::unify(&lhs_func, &rhs_func, substitutions)?;
                Self::normalize_substitutions(substitutions);
                Ok(())
            }
            (func, Ty::Closure { func: closure, .. })
            | (Ty::Closure { func: closure, .. }, func)
                if matches!(func, Ty::Func(_, _, _)) =>
            {
                Self::unify(&func, &closure, substitutions)?;
                Self::normalize_substitutions(substitutions);
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
            (Ty::Struct(_, lhs), Ty::Struct(_, rhs)) if lhs.len() == rhs.len() => {
                for (lhs, rhs) in lhs.iter().zip(rhs) {
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
            Ty::Func(params, returning, generics) => {
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
    fn substitute_ty_with_map(ty: &Ty, substitutions: &HashMap<TypeVarID, Ty>) -> Ty {
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
                let captures = captures
                    .iter()
                    .map(|capture| Self::substitute_ty_with_map(capture, substitutions))
                    .collect();

                Ty::Closure { func, captures }
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
