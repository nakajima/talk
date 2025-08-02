//! Constraint solver for the type checking system.
//!
//! This module implements a constraint solver that processes type constraints
//! generated during type checking. It handles various constraint types including
//! equality, conformance, member access, and pattern matching.

use tracing::Level;

use crate::{
    ExprMetaStorage, SymbolID,
    conformance::Conformance,
    conformance_checker::{ConformanceChecker, ConformanceError},
    constraint::Constraint,
    environment::{Environment, TypeParameter},
    name::Name,
    parsing::expr_id::ExprID,
    row::Label,
    row_constraints::RowConstraintSolver,
    semantic_index::ResolvedExpr,
    substitutions::Substitutions,
    ty::Primitive,
    ty::{RowKind, Ty},
    type_checker::{Scheme, TypeError},
    type_def::TypeDef,
    type_var_id::{TypeVarID, TypeVarKind},
};

/// The result of running the constraint solver.
pub struct ConstraintSolverSolution {
    /// Constraints that could not be solved
    pub unsolved_constraints: Vec<Constraint>,
    /// Type substitutions derived from solving constraints
    pub substitutions: Substitutions,
    /// Type errors encountered during solving
    pub errors: Vec<(ExprID, TypeError)>,
}

/// The constraint solver processes type constraints to infer types.
pub struct ConstraintSolver<'a> {
    /// The type environment containing type definitions and bindings
    env: &'a mut Environment,
    /// Metadata storage for expression information
    meta: &'a ExprMetaStorage,
    /// Stack of constraints to be solved
    constraints: Vec<Constraint>,
    /// Generation counter for type variables
    generation: u32,
    /// Solved row constraints for member resolution
    row_constraints: Vec<crate::row::RowConstraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(env: &'a mut Environment, meta: &'a ExprMetaStorage, generation: u32) -> Self {
        Self {
            constraints: env.constraints().clone(),
            env,
            meta,
            generation,
            row_constraints: Vec::new(),
        }
    }

    /// Determines if a constraint should be deferred based on its dependencies.
    /// Some constraints need to wait for other type information to be resolved first.
    fn should_defer_constraint(
        &mut self,
        constraint: &Constraint,
        substitutions: &mut Substitutions,
    ) -> bool {
        match constraint {
            Constraint::MemberAccess(_, receiver_ty, _, _) => {
                let resolved_receiver = substitutions.apply(receiver_ty, 0, &mut self.env.context);
                // Defer if receiver is still an unresolved TypeVar that's not a placeholder/instance
                if let Ty::TypeVar(tv) = &resolved_receiver {
                    match &tv.kind {
                        TypeVarKind::Member(_) | TypeVarKind::CallReturn | TypeVarKind::Let => {
                            // These are intermediate TypeVars that should be resolved first
                            tracing::trace!(
                                "Deferring MemberAccess on intermediate TypeVar: {:?}",
                                tv
                            );
                            return true;
                        }
                        _ => {
                            // Also defer if there are any unprocessed row constraints for this type var
                            let has_row_constraints = self.constraints.iter().any(|c| {
                                matches!(c, Constraint::Row { constraint, .. } if {
                                    use crate::row::RowConstraint;
                                    match constraint {
                                        RowConstraint::HasField { type_var, .. } |
                                        RowConstraint::HasRow { type_var, .. } |
                                        RowConstraint::HasExactRow { type_var, .. } => type_var == tv,
                                        RowConstraint::RowConcat { result, .. } => result == tv,
                                        RowConstraint::RowRestrict { result, .. } => result == tv,
                                        _ => false,
                                    }
                                })
                            });

                            if has_row_constraints {
                                tracing::trace!(
                                    "Deferring MemberAccess on TypeVar with pending row constraints: {:?}",
                                    tv
                                );
                                return true;
                            }
                        }
                    }
                }
                false
            }
            Constraint::Row { constraint, .. } => {
                use crate::row::RowConstraint;
                match constraint {
                    RowConstraint::RowConcat { left, right, .. } => {
                        // Defer RowConcat if we haven't processed HasField constraints for left/right yet
                        let has_pending_fields = self.constraints.iter().any(|c| {
                            matches!(c, Constraint::Row { constraint: rc, .. } if {
                                match rc {
                                    RowConstraint::HasField { type_var, .. } =>
                                        type_var == left || type_var == right,
                                    _ => false,
                                }
                            })
                        });

                        if has_pending_fields {
                            tracing::trace!(
                                "Deferring RowConcat until HasField constraints are processed"
                            );
                            return true;
                        }
                    }
                    RowConstraint::RowRestrict { source, .. } => {
                        // Defer RowRestrict if we haven't processed HasField constraints for source yet
                        let has_pending_fields = self.constraints.iter().any(|c| {
                            matches!(c, Constraint::Row { constraint: rc, .. } if {
                                match rc {
                                    RowConstraint::HasField { type_var, .. } => type_var == source,
                                    _ => false,
                                }
                            })
                        });

                        if has_pending_fields {
                            tracing::trace!(
                                "Deferring RowRestrict until HasField constraints are processed"
                            );
                            return true;
                        }
                    }
                    _ => {}
                }
                false
            }
            _ => false,
        }
    }

    /// Solves all constraints and returns the solution.
    /// Uses an iterative approach with constraint deferral to handle dependencies.
    pub fn solve(&mut self) -> ConstraintSolverSolution {
        let mut substitutions = Substitutions::new();
        let mut errors = vec![];
        let mut unsolved_constraints = vec![];
        let mut deferred_constraints = Vec::new();
        let mut made_progress = true;
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 10;

        // Process constraints with dependency awareness
        while made_progress && iterations < MAX_ITERATIONS {
            made_progress = false;
            iterations += 1;

            // Process main constraints
            while let Some(constraint) = self.constraints.pop() {
                if self.should_defer_constraint(&constraint, &mut substitutions) {
                    deferred_constraints.push(constraint);
                    continue;
                }
                match self.solve_constraint(&constraint, &mut substitutions) {
                    Ok(_) => (),
                    Err(err) => {
                        // Row constraint errors should never be deferred - they are immediate failures
                        let is_row_constraint = matches!(&constraint, Constraint::Row { .. });

                        // For MemberAccess on TypeVars, keep deferring as long as possible
                        // since the TypeVar might be resolved in a later iteration
                        let should_defer = if is_row_constraint {
                            false // Never defer row constraint errors
                        } else if let Constraint::MemberAccess(_, receiver_ty, member_name, _) =
                            &constraint
                        {
                            let resolved =
                                substitutions.apply(receiver_ty, 0, &mut self.env.context);
                            if matches!(resolved, Ty::TypeVar(_)) && iterations < MAX_ITERATIONS - 1
                            {
                                tracing::trace!(
                                    "Deferring MemberAccess({}) on TypeVar in iteration {}",
                                    member_name,
                                    iterations
                                );
                                true
                            } else {
                                false
                            }
                        } else {
                            false
                        };

                        if (iterations == 1 && !is_row_constraint) || should_defer {
                            deferred_constraints.push(constraint.clone());
                        } else {
                            unsolved_constraints.push(constraint.clone());
                            let processed_err = match err {
                                TypeError::Defer(e) => TypeError::ConformanceError(vec![e]),
                                other => other,
                            };
                            errors.push((*constraint.expr_id(), processed_err))
                        }
                    }
                }

                made_progress = true;
            }

            // Process deferred constraints if we have any
            if !deferred_constraints.is_empty() && made_progress {
                tracing::trace!(
                    "Processing {} deferred constraints in iteration {}",
                    deferred_constraints.len(),
                    iterations
                );
                self.constraints
                    .extend(deferred_constraints.drain(..).rev());
                made_progress = true;
            }
        }

        // Any remaining deferred constraints are unsolved
        for constraint in deferred_constraints {
            unsolved_constraints.push(constraint.clone());
            errors.push((
                *constraint.expr_id(),
                TypeError::Unknown(format!(
                    "Could not solve deferred constraint: {constraint:?}"
                )),
            ));
        }

        let mut remaining_type_vars = vec![];

        for (_id, typed_expr) in &mut self.env.typed_exprs.iter_mut() {
            typed_expr.ty = substitutions.apply(&typed_expr.ty, 0, &mut self.env.context);

            if let Ty::TypeVar(var) = &typed_expr.ty {
                remaining_type_vars.push(var.clone());
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

    /// Processes a single constraint by dispatching to the appropriate handler.
    #[tracing::instrument(level = Level::TRACE, skip(self, substitutions), fields(result))]
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
                    self.solve_type_var_conformance(type_var, conformance, substitutions)?;
                } else {
                    let conformance_checker = ConformanceChecker::new(ty, conformance, self.env);
                    let unifications = conformance_checker.check()?;
                    for (lhs, rhs) in unifications {
                        substitutions.unify(&lhs, &rhs, &mut self.env.context, self.generation)?;
                    }
                }
            }
            Constraint::Equality(expr_id, lhs, rhs) => {
                let lhs = substitutions.apply(lhs, 0, &mut self.env.context);
                let rhs = substitutions.apply(rhs, 0, &mut self.env.context);

                substitutions
                    .unify(&lhs, &rhs, &mut self.env.context, self.generation)
                    .map_err(|err| {
                        let meta = self.meta.get(expr_id);

                        tracing::error!("Equality check failed {expr_id:?} {err:?}\n{meta:?}");
                        err
                    })?;
            }
            Constraint::InstanceOf { scheme, ty, .. } => {
                let mut mapping = Substitutions::new();
                for unbound_var in &scheme.unbound_vars() {
                    mapping.insert(
                        unbound_var.clone(),
                        Ty::TypeVar(
                            self.env
                                .new_type_variable(TypeVarKind::Unbound, unbound_var.expr_id),
                        ),
                    );
                }
                let instantiated_ty = Self::substitute_ty_with_map(ty, &mapping);

                substitutions.unify(
                    ty,
                    &instantiated_ty,
                    &mut self.env.context,
                    self.generation,
                )?;
            }
            Constraint::UnqualifiedMember(_node_id, member_name, result_ty) => {
                let result_ty = substitutions.apply(result_ty, 0, &mut self.env.context);
                self.solve_unqualified_member(&result_ty, member_name, substitutions)?;
            }
            Constraint::MemberAccess(node_id, receiver_ty, member_name, result_ty) => {
                let receiver_ty = substitutions.apply(receiver_ty, 0, &mut self.env.context);
                let result_ty = substitutions.apply(result_ty, 0, &mut self.env.context);

                let (member_ty, type_params, type_args) =
                    self.resolve_member_type(&receiver_ty, member_name, substitutions, node_id)?;

                let mut member_substitutions = substitutions.clone();
                for (type_param, type_arg) in type_params.iter().zip(type_args) {
                    member_substitutions.insert(type_param.type_var.clone(), type_arg.clone());
                }

                let specialized_ty =
                    member_substitutions.apply(&member_ty, 0, &mut self.env.context);
                substitutions.unify(
                    &result_ty,
                    &specialized_ty,
                    &mut self.env.context,
                    self.generation,
                )?;

                // Try to find the member symbol and update the semantic index
                if let Some(member_symbol) = self.find_member_symbol(&receiver_ty, member_name) {
                    // Update the semantic index with the resolved symbol
                    if let Some(ResolvedExpr::MemberAccess {
                        receiver,
                        member_name: name,
                        resolved_symbol: _,
                        ty,
                    }) = self.env.semantic_index.get_expression(node_id).cloned()
                    {
                        self.env.semantic_index.record_expression(
                            *node_id,
                            ResolvedExpr::MemberAccess {
                                receiver,
                                member_name: name,
                                resolved_symbol: Some(member_symbol),
                                ty,
                            },
                        );
                    }
                }
            }
            Constraint::InitializerCall {
                initializes_id,
                args,
                func_ty,
                result_ty,
                type_args,
                ..
            } => {
                self.solve_initializer_call(
                    initializes_id,
                    args,
                    func_ty,
                    result_ty,
                    type_args,
                    substitutions,
                )?;
            }
            Constraint::VariantMatch {
                scrutinee_ty,
                variant_name,
                field_tys,
                ..
            } => {
                let scrutinee_ty = substitutions.apply(scrutinee_ty, 0, &mut self.env.context);
                self.solve_variant_match(&scrutinee_ty, variant_name, field_tys, substitutions)?;
            }
            Constraint::Row {
                constraint,
                expr_id,
            } => {
                use crate::row::RowConstraint;
                tracing::trace!("Solving row constraint: {:?}", constraint);

                // Store the current constraint for member resolution
                self.row_constraints.push(constraint.clone());
                // Also store in the environment for later access
                self.env.row_constraints.push(constraint.clone());

                // Use the row constraint solver for all row constraints
                let mut row_solver = RowConstraintSolver::new(self.env, self.generation);

                // Pass all row constraints to the solver for exactness checking
                row_solver.set_all_constraints(&self.row_constraints);

                // First populate the row solver with existing row constraints
                // This ensures operations like RowConcat and RowRestrict can see necessary fields
                for existing_constraint in &self.row_constraints[..self.row_constraints.len() - 1] {
                    // Process all constraints to build up the row solver's state
                    // If any constraint fails, we should propagate the error
                    row_solver.solve_row_constraint(
                        existing_constraint,
                        ExprID(0),
                        substitutions,
                    )?;
                }

                // Now solve the current constraint
                row_solver.solve_row_constraint(constraint, *expr_id, substitutions)?;

                // Collect new constraints to add after row solver is done
                let mut new_constraints = Vec::new();

                // Update our stored constraints with the result fields
                match constraint {
                    RowConstraint::RowConcat { result, .. } => {
                        if let Some(result_fields) = row_solver.get_resolved_fields(result) {
                            for (label, field_info) in result_fields {
                                let new_constraint = RowConstraint::HasField {
                                    type_var: result.clone(),
                                    label: label.clone(),
                                    field_ty: field_info.ty.clone(),
                                    metadata: field_info.metadata.clone(),
                                };
                                if !self.row_constraints.contains(&new_constraint) {
                                    self.row_constraints.push(new_constraint.clone());
                                    new_constraints.push(new_constraint);
                                }
                            }
                        }
                    }
                    RowConstraint::RowRestrict { result, .. } => {
                        if let Some(result_fields) = row_solver.get_resolved_fields(result) {
                            for (label, field_info) in result_fields {
                                let new_constraint = RowConstraint::HasField {
                                    type_var: result.clone(),
                                    label: label.clone(),
                                    field_ty: field_info.ty.clone(),
                                    metadata: field_info.metadata.clone(),
                                };
                                if !self.row_constraints.contains(&new_constraint) {
                                    self.row_constraints.push(new_constraint.clone());
                                    new_constraints.push(new_constraint);
                                }
                            }
                        }
                    }
                    _ => {}
                }

                // Now add the new constraints to the environment
                for new_constraint in new_constraints {
                    self.env.row_constraints.push(new_constraint);
                }

                tracing::trace!("Row constraint handled");
            }
            Constraint::Mutability {
                expr_id,
                receiver_ty,
                field_name,
            } => {
                let receiver_ty = substitutions.apply(receiver_ty, 0, &mut self.env.context);
                self.solve_mutability_constraint(&receiver_ty, field_name, *expr_id)?;
            }
        };

        Ok(())
    }

    fn solve_initializer_call(
        &mut self,
        initializes_id: &SymbolID,
        args: &[Ty],
        func_ty: &Ty,
        result_ty: &Ty,
        type_args: &[Ty],
        substitutions: &mut Substitutions,
    ) -> Result<(), TypeError> {
        let struct_def = self
            .env
            .lookup_struct(initializes_id)
            .ok_or_else(|| {
                TypeError::Unresolved("Struct definition not found for initialization".into())
            })?
            .clone();

        // TODO: Support multiple initializers
        let initializers = struct_def.initializers();
        if initializers.is_empty() {
            return Err(TypeError::Unknown(format!(
                "No initializers found for struct {}",
                struct_def.name().unwrap_or("<unknown>")
            )));
        }

        let initializer = &initializers[0];
        let Ty::Init(_, params) = initializer else {
            return Err(TypeError::Unknown("Invalid initializer type".into()));
        };

        // Check argument count
        if args.len() != params.len() {
            return Err(TypeError::ArgumentError(format!(
                "Expected {} arguments, got {}",
                params.len(),
                args.len()
            )));
        }

        // Unify parameter types with argument types
        for (param, arg) in params.iter().zip(args) {
            let param = substitutions.apply(param, 0, &mut self.env.context);
            let arg = substitutions.apply(arg, 0, &mut self.env.context);
            substitutions.unify(&param, &arg, &mut self.env.context, self.generation)?;
        }

        // Unify initializer type with function type
        substitutions.unify(
            initializer,
            func_ty,
            &mut self.env.context,
            self.generation,
        )?;

        // Create and unify the specialized struct type
        let struct_with_generics = Ty::struct_type(
            *initializes_id,
            struct_def.name().to_string(),
            type_args.to_vec(),
        );
        let specialized_struct = self.env.instantiate(&Scheme::new(
            struct_with_generics,
            struct_def.canonical_type_variables(),
            vec![],
        ));

        substitutions.unify(
            result_ty,
            &specialized_struct,
            &mut self.env.context,
            self.generation,
        )?;

        Ok(())
    }

    fn solve_variant_match(
        &mut self,
        scrutinee_ty: &Ty,
        variant_name: &str,
        field_tys: &[Ty],
        substitutions: &mut Substitutions,
    ) -> Result<(), TypeError> {
        let Ty::Row {
            generics: concrete_type_args,
            kind: RowKind::Enum(enum_id, _),
            ..
        } = scrutinee_ty
        else {
            return Err(TypeError::Unknown(format!(
                "VariantMatch expected an enum, but got {scrutinee_ty:?}"
            )));
        };

        let enum_def = self
            .env
            .lookup_enum(enum_id)
            .ok_or_else(|| TypeError::Unknown("Enum definition not found".into()))?;

        let (variant_tag, variant_ty) = enum_def
            .find_variant(variant_name)
            .ok_or_else(|| TypeError::UnknownVariant(Name::Raw(variant_name.to_string())))?;

        // Extract the generic field types from the variant's definition
        let generic_field_tys = match &variant_ty {
            Ty::Func(params, _, _) => params.clone(),
            Ty::Row {
                kind: RowKind::Enum(_, _),
                ..
            } => vec![], // Variant with no parameters
            _ => return Err(TypeError::Unknown("Invalid variant type".into())),
        };

        // Create substitutions for the enum's type parameters
        let mut local_substitutions = Substitutions::new();
        for (type_param, concrete_arg) in enum_def.type_parameters.iter().zip(concrete_type_args) {
            local_substitutions.insert(type_param.type_var.clone(), concrete_arg.clone());
        }

        // Specialize the variant's field types
        let specialized_field_tys = generic_field_tys
            .iter()
            .map(|ty| Self::substitute_ty_with_map(ty, &local_substitutions))
            .collect::<Vec<_>>();

        // Check field count
        if specialized_field_tys.len() != field_tys.len() {
            return Err(TypeError::Unknown(
                "Variant pattern has incorrect number of fields.".into(),
            ));
        }

        // Unify field types
        for (specialized_ty, pattern_ty) in specialized_field_tys.iter().zip(field_tys) {
            substitutions.unify(
                specialized_ty,
                pattern_ty,
                &mut self.env.context,
                self.generation,
            )?;
        }

        Ok(())
    }

    fn solve_unqualified_member(
        &mut self,
        result_ty: &Ty,
        member_name: &str,
        substitutions: &mut Substitutions,
    ) -> Result<(), TypeError> {
        match result_ty {
            // A variant with no values
            Ty::Row {
                kind: RowKind::Enum(enum_id, _),
                ..
            } => {
                let enum_def = self.env.lookup_enum(enum_id).ok_or_else(|| {
                    TypeError::Unknown(format!("Unable to resolve enum with id: {enum_id:?}"))
                })?;

                if let Some(variant) = enum_def.find_variant(member_name).cloned() {
                    substitutions.unify(
                        result_ty,
                        &variant.ty,
                        &mut self.env.context,
                        self.generation,
                    )?;
                }
            }
            // A variant with values (function type returning enum)
            Ty::Func(_, ret, _) => {
                let ret_ty = substitutions.apply(ret, 0, &mut self.env.context);
                if let Ty::Row {
                    kind: RowKind::Enum(enum_id, _),
                    ..
                } = ret_ty
                {
                    let enum_def = self.env.lookup_enum(&enum_id).ok_or_else(|| {
                        TypeError::Unknown(format!("Unable to resolve enum with id: {enum_id:?}"))
                    })?;

                    if let Some(variant) = enum_def.find_variant(member_name).cloned() {
                        substitutions.unify(
                            result_ty,
                            &variant.ty,
                            &mut self.env.context,
                            self.generation,
                        )?;
                    }
                } else {
                    tracing::error!("Expected enum return type, got: {:?}", ret_ty);
                }
            }
            _ => (),
        }
        Ok(())
    }

    fn resolve_member_type(
        &mut self,
        receiver_ty: &Ty,
        member_name: &str,
        substitutions: &Substitutions,
        expr_id: &ExprID,
    ) -> Result<(Ty, Vec<TypeParameter>, Vec<Ty>), TypeError> {
        tracing::debug!(
            "resolve_member_type: receiver_ty = {:?}, member = {}",
            receiver_ty,
            member_name
        );
        match receiver_ty {
            builtin @ Ty::Primitive(_) => {
                self.resolve_builtin_member(builtin, member_name)
            }
            Ty::Row {
                generics,
                kind: RowKind::Enum(enum_id, _),
                ..
            } => self.resolve_enum_member(enum_id, member_name, generics),
            Ty::TypeVar(type_var) => {
                tracing::debug!("Resolving member {} on TypeVar {:?}", member_name, type_var);
                let result =
                    self.resolve_type_var_member(type_var, member_name, substitutions, expr_id);
                tracing::debug!("TypeVar member resolution result: {:?}", result);
                result
            }
            Ty::Row {
                kind,
                generics,
                ..
            } => {
                if let RowKind::Enum(type_id, _)
                | RowKind::Struct(type_id, _)
                | RowKind::Protocol(type_id, _) = kind
                {
                    // Nominal row - use typedef resolution
                    self.resolve_type_member(type_id, member_name, generics, substitutions, expr_id)
                } else {
                    // Structural row - look up field directly from constraints
                    if let Some(field_ty) = receiver_ty.get_row_field_type(member_name) {
                        Ok((field_ty, vec![], vec![]))
                    } else {
                        Err(TypeError::MemberNotFound(
                            receiver_ty.to_string(),
                            member_name.to_string(),
                        ))
                    }
                }
            }
            _ => Err(TypeError::MemberNotFound(
                receiver_ty.to_string(),
                member_name.to_string(),
            )),
        }
    }

    fn resolve_builtin_member(
        &mut self,
        builtin: &Ty,
        member_name: &str,
    ) -> Result<(Ty, Vec<TypeParameter>, Vec<Ty>), TypeError> {
        let symbol_id = match builtin {
            Ty::Primitive(Primitive::Int) => SymbolID::INT,
            Ty::Primitive(Primitive::Float) => SymbolID::FLOAT,
            Ty::Primitive(Primitive::Bool) => SymbolID::BOOL,
            Ty::Primitive(Primitive::Pointer) => SymbolID::POINTER,
            _ => unreachable!("Invalid builtin type"),
        };

        // TODO: Look up member from row constraints instead of type def
        Err(TypeError::Unknown("Builtin member lookup not yet implemented for constraint-based rows".into()))
    }

    fn resolve_type_member(
        &mut self,
        type_id: &SymbolID,
        member_name: &str,
        generics: &[Ty],
        substitutions: &Substitutions,
        expr_id: &ExprID,
    ) -> Result<(Ty, Vec<TypeParameter>, Vec<Ty>), TypeError> {
        // TODO: Get type info from row constraints instead of type def
        // For now, return an error
        Err(TypeError::Unknown("Type member lookup not yet implemented for constraint-based rows".into()))
    }

    fn resolve_enum_member(
        &self,
        enum_id: &SymbolID,
        member_name: &str,
        generics: &[Ty],
    ) -> Result<(Ty, Vec<TypeParameter>, Vec<Ty>), TypeError> {
        let enum_def = self.env.lookup_enum(enum_id).ok_or_else(|| {
            TypeError::Unknown(format!("Unable to resolve enum with id: {enum_id:?}"))
        })?;

        let member_ty = enum_def.member_ty(member_name).ok_or_else(|| {
            TypeError::Unknown(format!(
                "Member not found for enum {}: {}",
                enum_def.name().unwrap_or("<unknown>"), member_name
            ))
        })?;

        Ok((
            member_ty.clone(),
            enum_def.type_parameters.clone(),
            generics.to_vec(),
        ))
    }

    #[allow(clippy::type_complexity)]
    fn resolve_type_var_member(
        &mut self,
        type_var: &TypeVarID,
        member_name: &str,
        substitutions: &Substitutions,
        expr_id: &ExprID,
    ) -> Result<(Ty, Vec<TypeParameter>, Vec<Ty>), TypeError> {
        // Check if this is a row type variable that needs a field constraint
        if matches!(type_var.kind, TypeVarKind::Row) {
            // Check if we already have a field constraint for this member
            let has_field_constraint = self.row_constraints.iter().any(|rc| {
                matches!(rc, RowConstraint::HasField { type_var: tv, label, .. }
                    if tv == type_var && label == member_name)
            });

            if !has_field_constraint {
                // Generate a new field type variable
                let field_ty = Ty::TypeVar(
                    self.env
                        .new_type_variable(TypeVarKind::Member(member_name.to_string()), *expr_id),
                );

                // Add the HasField constraint
                let new_constraint = RowConstraint::HasField {
                    type_var: type_var.clone(),
                    label: Label::from(member_name.to_string()),
                    field_ty: field_ty.clone(),
                    metadata: Default::default(),
                };

                self.constraints.push(Constraint::Row {
                    expr_id: *expr_id,
                    constraint: new_constraint.clone(),
                });

                // Also add to row_constraints for immediate lookup
                self.row_constraints.push(new_constraint);

                return Ok((field_ty, vec![], vec![]));
            }
        }

        let matching_constraints = self
            .constraints
            .iter()
            .filter(|constraint| constraint.contains(|t| *t == Ty::TypeVar(type_var.clone())))
            .collect::<Vec<_>>();

        for constraint in matching_constraints {
            match constraint {
                Constraint::ConformsTo { conformance, .. } => {
                    if let Some((ty, params, assoc_types)) = self.resolve_protocol_member(
                        &conformance.protocol_id,
                        member_name,
                        &conformance.associated_types,
                    )? {
                        return Ok((ty, params, assoc_types));
                    }
                }
                Constraint::InstanceOf {
                    symbol_id, scheme, ..
                } => {
                    // TODO: Look up type members from row constraints
                    // For now, return an error
                    return Err(TypeError::Unknown(
                        "Type member lookup not yet implemented for constraint-based types".into()
                    ));
                }
                _ => (),
            }
        }

        // Check stored row constraints
        use crate::row::RowConstraint;
        tracing::trace!(
            "Checking row constraints for type_var {:?}, member {}",
            type_var,
            member_name
        );
        tracing::trace!("Available row constraints: {:?}", self.row_constraints);

        for row_constraint in &self.row_constraints {
            match row_constraint {
                RowConstraint::HasField {
                    type_var: tv,
                    label,
                    field_ty,
                    ..
                } if tv == type_var && label == member_name => {
                    tracing::trace!("Found matching HasField constraint!");
                    // Apply current substitutions to the field type
                    let resolved_ty = Self::substitute_ty_with_map(field_ty, substitutions);
                    return Ok((resolved_ty, vec![], vec![]));
                }
                RowConstraint::HasRow {
                    type_var: tv, row, ..
                }
                | RowConstraint::HasExactRow { type_var: tv, row }
                    if tv == type_var =>
                {
                    if let Some(field) = row.get_field(&member_name.to_string()) {
                        tracing::trace!("Found field in row constraint!");
                        // Apply current substitutions to the field type
                        let resolved_ty = Self::substitute_ty_with_map(&field.ty, substitutions);
                        return Ok((resolved_ty, vec![], vec![]));
                    }
                }
                _ => {}
            }
        }

        // For TypeVars that haven't been resolved yet, we should defer rather than
        // report MemberNotFound, as the TypeVar might be unified with a concrete type
        // that has the member in a later iteration
        Err(TypeError::Defer(ConformanceError::TypeCannotConform(
            format!(
                "TypeVar {} member '{}' not yet resolved",
                type_var.id, member_name
            ),
        )))
    }

    #[allow(clippy::type_complexity)]
    fn resolve_protocol_member(
        &self,
        protocol_id: &SymbolID,
        member_name: &str,
        associated_types: &[Ty],
    ) -> Result<Option<(Ty, Vec<TypeParameter>, Vec<Ty>)>, TypeError> {
        // TODO: Get protocol info from row constraints
        // For now, return None since we don't have protocol definitions
        Ok(None)
    }

    fn solve_type_var_conformance(
        &mut self,
        type_var: &TypeVarID,
        conformance: &Conformance,
        substitutions: &mut Substitutions,
    ) -> Result<(), TypeError> {
        let candidates = self.find_conforming_types(conformance, substitutions)?;

        match candidates.len() {
            0 => Err(TypeError::Defer(ConformanceError::TypeCannotConform(
                Ty::TypeVar(type_var.clone()).to_string(),
            ))),
            1 => {
                let (candidate_ty, candidate_unifs, type_def_conf) = &candidates[0];
                self.apply_conformance_solution(
                    type_var,
                    candidate_ty,
                    candidate_unifs,
                    conformance,
                    type_def_conf,
                    substitutions,
                )
            }
            _ => Ok(()), // Multiple candidates: leave generic
        }
    }

    #[allow(clippy::type_complexity)]
    fn find_conforming_types(
        &mut self,
        conformance: &Conformance,
        substitutions: &mut Substitutions,
    ) -> Result<Vec<(Ty, Vec<(Ty, Ty)>, Conformance)>, TypeError> {
        // TODO: Replace with constraint-based type lookup
        let types: Vec<(TypeDef, Conformance)> = vec![]; // Placeholder
        // Was: self.env.types.values().filter_map(|t| ...)
        // This needs to be reimplemented using row constraints

        tracing::trace!("Possible conforming types: {types:?}");

        let mut conforming_candidates = vec![];
        for (type_def, type_def_conformance) in types {
            let type_def_ty = type_def.ty();
            let conformance_checker =
                ConformanceChecker::new(&type_def_ty, &type_def_conformance, self.env);

            match conformance_checker.check() {
                Ok(unifications) => {
                    conforming_candidates.push((type_def_ty, unifications, type_def_conformance));
                }
                Err(e) => {
                    tracing::error!("Conformance check failed: {e:?}");
                }
            }
        }

        Ok(conforming_candidates)
    }

    fn apply_conformance_solution(
        &mut self,
        type_var: &TypeVarID,
        candidate_ty: &Ty,
        candidate_unifications: &[(Ty, Ty)],
        conformance: &Conformance,
        type_def_conformance: &Conformance,
        substitutions: &mut Substitutions,
    ) -> Result<(), TypeError> {
        // Unify the type variable with the candidate type
        substitutions.unify(
            &Ty::TypeVar(type_var.clone()),
            candidate_ty,
            &mut self.env.context,
            self.generation,
        )?;

        // Unify associated types
        for (provided, required) in conformance
            .associated_types
            .iter()
            .zip(type_def_conformance.associated_types.iter())
        {
            substitutions.unify(provided, required, &mut self.env.context, self.generation)?;
        }

        // Apply candidate unifications
        for (lhs, rhs) in candidate_unifications {
            substitutions.unify(lhs, rhs, &mut self.env.context, self.generation)?;
        }

        Ok(())
    }

    /// Applies a given substitution map to a type. Does not recurse on type variables already in the map.
    #[tracing::instrument(level = Level::TRACE, fields(result))]
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
            Ty::Method { self_ty, func } => Ty::Method {
                self_ty: Self::substitute_ty_with_map(self_ty, substitutions).into(),
                func: Self::substitute_ty_with_map(func, substitutions).into(),
            },
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
            Ty::Row {
                type_var,
                constraints,
                generics,
                kind,
            } => {
                let applied_generics = generics
                    .iter()
                    .map(|g| Self::substitute_ty_with_map(g, substitutions))
                    .collect();
                // TODO: Also substitute types within constraints
                Ty::Row {
                    type_var: type_var.clone(),
                    constraints: constraints.clone(),
                    generics: applied_generics,
                    kind: kind.clone(),
                }
            }
            Ty::Tuple(types) => Ty::Tuple(
                types
                    .iter()
                    .map(|param| Self::substitute_ty_with_map(param, substitutions))
                    .collect(),
            ),
            Ty::Array(ty) => Ty::Array(Self::substitute_ty_with_map(ty, substitutions).into()),
            Ty::Primitive(_) | Ty::SelfType => {
                ty.clone()
            }
        }
    }

    /// Find the symbol ID for a member of a type
    fn find_member_symbol(&self, receiver_ty: &Ty, member_name: &str) -> Option<SymbolID> {
        match receiver_ty {
            Ty::Row {
                kind:
                    RowKind::Struct(type_id, _)
                    | RowKind::Protocol(type_id, _)
                    | RowKind::Enum(type_id, _),
                ..
            } => {
                // TODO: Look up the type definition from row constraints
                // For now, return None as we don't have type definitions
                None
                // Was: let type_def = self.env.types.get(type_id)?;
                // Then checked for property, method, or variant
            }
            Ty::Row {
                kind: RowKind::Record,
                ..
            } => {
                // Structural row fields don't have symbol IDs
                None
            }
            _ => None,
        }
    }

    /// Solve mutability constraints by checking if a field assignment is valid
    fn solve_mutability_constraint(
        &mut self,
        receiver_ty: &Ty,
        field_name: &str,
        _expr_id: ExprID,
    ) -> Result<(), TypeError> {
        // For struct types, check if the field is mutable
        // match receiver_ty {
        //     Ty::Row {
        //         kind: RowKind::Struct(symbol_id, _),
        //         ..
        //     } => {
        //         // Look up the struct definition
        //         let struct_def = self.env.lookup_struct(symbol_id).ok_or_else(|| {
        //             TypeError::MutabilityError(
        //                 "Cannot find struct definition for mutability check".to_string(),
        //             )
        //         })?;

        //         // Find the field in the struct properties
        //         let properties = struct_def.properties();
        //         let field = properties.iter().find(|prop| prop.name == field_name);

        //         if let Some(_field) = field {
        //             todo!();
        //         } else {
        //             return Err(TypeError::MutabilityError(format!(
        //                 "Field '{}' not found in struct",
        //                 field_name
        //             )));
        //         }
        //     }
        //     // For type variables, we can't check yet - this constraint should be retried later
        //     Ty::TypeVar(_) => {
        //         return Err(TypeError::Defer(ConformanceError::TypeCannotConform(
        //             "Type variable not yet resolved for mutability check".to_string(),
        //         )));
        //     }
        //     _ => {
        //         return Err(TypeError::MutabilityError(format!(
        //             "Cannot assign to field of non-struct type"
        //         )));
        //     }
        // }

        Ok(())
    }
}
