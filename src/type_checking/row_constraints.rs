//! Row constraint solving for the qualified types system.
//!
//! This module integrates row constraints into the main constraint solver,
//! treating row structure as qualifications on type variables.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{
    constraint::Constraint,
    environment::Environment,
    expr_id::ExprID,
    row::{FieldInfo, Label, LabelSet, RowConstraint, RowSpec},
    substitutions::Substitutions,
    ty::Ty,
    type_checker::TypeError,
    type_var_id::{TypeVarID, TypeVarKind},
};

/// Extended constraint type that includes row constraints
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtendedConstraint {
    /// Standard type constraint
    Base(Constraint),
    /// Row-specific constraint
    Row(RowConstraint),
}

/// Solver for row constraints integrated with the main type system
pub struct RowConstraintSolver<'a> {
    /// Tracks which fields each type variable has
    type_var_fields: HashMap<TypeVarID, BTreeMap<Label, FieldInfo>>,
    /// Tracks which fields each type variable lacks
    type_var_lacks: HashMap<TypeVarID, LabelSet>,
    /// Tracks which type variables have exact rows (no additional fields allowed)
    type_var_exact: HashMap<TypeVarID, bool>,
    /// All row constraints being processed (for exactness checking)
    all_constraints: Vec<RowConstraint>,
    /// Tracks which type variables extend other type variables
    type_var_extensions: HashMap<TypeVarID, Vec<TypeVarID>>,
    /// Cache for get_all_fields results
    all_fields_cache: HashMap<TypeVarID, BTreeMap<Label, FieldInfo>>,
    /// Phantom data to keep the lifetime parameter
    _phantom: std::marker::PhantomData<&'a ()>,
}

impl<'a> RowConstraintSolver<'a> {
    pub fn new(_env: &'a mut Environment, _generation: u32) -> Self {
        Self {
            type_var_fields: HashMap::new(),
            type_var_lacks: HashMap::new(),
            type_var_exact: HashMap::new(),
            all_constraints: Vec::new(),
            type_var_extensions: HashMap::new(),
            all_fields_cache: HashMap::new(),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Set all constraints for exactness checking
    pub fn set_all_constraints(&mut self, constraints: &[RowConstraint]) {
        self.all_constraints = constraints.to_vec();
    }

    /// Main entry point for solving a row constraint
    pub fn solve_row_constraint(
        &mut self,
        constraint: &RowConstraint,
        expr_id: ExprID,
        type_subs: &mut Substitutions,
    ) -> Result<(), TypeError> {
        tracing::trace!("solve_row_constraint: {:?}", constraint);
        let result = match constraint {
            RowConstraint::HasField {
                type_var,
                label,
                field_ty,
                metadata,
            } => self.add_field_constraint(type_var, label, field_ty, metadata, expr_id),

            RowConstraint::HasRow {
                type_var,
                row,
                extension,
            } => self.add_row_constraint(type_var, row, extension.as_ref(), expr_id),

            RowConstraint::HasExactRow { type_var, row } => {
                self.add_exact_row_constraint(type_var, row, expr_id)
            }

            RowConstraint::Lacks { type_var, labels } => {
                self.add_lacks_constraint(type_var, labels)
            }

            RowConstraint::RowConcat {
                left,
                right,
                result,
            } => self.solve_row_concat(left, right, result, type_subs),

            RowConstraint::RowRestrict {
                source,
                labels,
                result,
            } => self.solve_row_restrict(source, labels, result),
        };

        if let Err(ref e) = result {
            tracing::trace!("Row constraint error: {:?}", e);
        }
        result
    }

    /// Add a field constraint to a type variable
    fn add_field_constraint(
        &mut self,
        type_var: &TypeVarID,
        label: &Label,
        field_ty: &Ty,
        metadata: &crate::row::FieldMetadata,
        expr_id: ExprID,
    ) -> Result<(), TypeError> {
        tracing::trace!(
            "add_field_constraint: type_var={:?}, label={}, exact={:?}",
            type_var,
            label,
            self.type_var_exact.get(type_var)
        );

        // Check if this type variable has an exact row constraint
        // First check our local state
        let mut is_exact = self.type_var_exact.get(type_var).copied().unwrap_or(false);

        // Also check if there's a HasExactRow constraint in all_constraints
        if !is_exact {
            is_exact = self.all_constraints.iter().any(
                |c| matches!(c, RowConstraint::HasExactRow { type_var: tv, .. } if tv == type_var),
            );
        }

        // Types with extensions cannot be exact
        if is_exact && self.type_var_extensions.contains_key(type_var) {
            return Err(TypeError::Unknown(format!(
                "Type variable {type_var:?} has exact row constraint but also has extensions, which is not allowed"
            )));
        }

        if is_exact {
            // Check if the field already exists or is part of the exact row definition
            let field_allowed = self
                .type_var_fields
                .get(type_var)
                .map(|fields| fields.contains_key(label))
                .unwrap_or(false)
                || self.all_constraints.iter().any(|c| match c {
                    RowConstraint::HasExactRow { type_var: tv, row } if tv == type_var => {
                        row.fields.contains_key(label)
                    }
                    _ => false,
                });

            if !field_allowed {
                tracing::trace!("Rejecting field '{}' due to exact row constraint", label);
                return Err(TypeError::Unknown(format!(
                    "Cannot add field '{label}' to type with exact row constraint"
                )));
            }
        }

        // Check lacks constraints
        if let Some(lacks) = self.type_var_lacks.get(type_var)
            && lacks.contains(label)
        {
            return Err(TypeError::Unknown(format!(
                "Type variable cannot have field '{label}' due to lacks constraint"
            )));
        }

        // Add or verify field
        let fields = self.type_var_fields.entry(type_var.clone()).or_default();

        if let Some(existing) = fields.get(label) {
            // Field already exists - check compatibility
            if &existing.ty != field_ty {
                return Err(TypeError::Unknown(format!(
                    "Conflicting types for field '{}': expected {:?}, found {:?}",
                    label, existing.ty, field_ty
                )));
            }
        } else {
            // Add new field
            fields.insert(
                label.clone(),
                FieldInfo {
                    ty: field_ty.clone(),
                    expr_id,
                    metadata: metadata.clone(),
                },
            );

            // Invalidate cache since we added a new field
            self.invalidate_cache(type_var);
        }

        Ok(())
    }

    /// Add a row constraint (has at least these fields)
    fn add_row_constraint(
        &mut self,
        type_var: &TypeVarID,
        row: &RowSpec,
        extension: Option<&TypeVarID>,
        _expr_id: ExprID,
    ) -> Result<(), TypeError> {
        // Add all fields from the row
        for (label, field) in &row.fields {
            self.add_field_constraint(type_var, label, &field.ty, &field.metadata, field.expr_id)?;
        }

        // If there's an extension, record that relationship
        if let Some(ext) = extension {
            // Check if this type variable has an exact row constraint
            if self.type_var_exact.get(type_var).copied().unwrap_or(false) {
                return Err(TypeError::Unknown(format!(
                    "Cannot add extension to type variable {type_var:?} which has exact row constraint",
                )));
            }

            // Check for cycles before adding extension
            if self.would_create_cycle(type_var, ext) {
                return Err(TypeError::Unknown(format!(
                    "Adding extension from {type_var:?} to {ext:?} would create a cycle",
                )));
            }

            // Track that type_var is extended by ext
            self.type_var_extensions
                .entry(type_var.clone())
                .or_default()
                .push(ext.clone());

            // Invalidate cache for affected type vars
            self.invalidate_cache(type_var);
        }

        Ok(())
    }

    /// Check if adding an extension would create a cycle
    fn would_create_cycle(&self, from: &TypeVarID, to: &TypeVarID) -> bool {
        // Check if 'to' can reach 'from' through existing extensions
        let mut visited = HashSet::new();
        self.can_reach(to, from, &mut visited)
    }

    /// Check if 'from' can reach 'target' through extensions
    fn can_reach(
        &self,
        from: &TypeVarID,
        target: &TypeVarID,
        visited: &mut HashSet<TypeVarID>,
    ) -> bool {
        if from == target {
            return true;
        }

        if !visited.insert(from.clone()) {
            return false; // Already visited, avoid infinite loop
        }

        if let Some(extensions) = self.type_var_extensions.get(from) {
            for ext in extensions {
                if self.can_reach(ext, target, visited) {
                    return true;
                }
            }
        }

        false
    }

    /// Invalidate cache for a type variable and all that depend on it
    fn invalidate_cache(&mut self, type_var: &TypeVarID) {
        // Remove from cache
        self.all_fields_cache.remove(type_var);

        // Invalidate any type vars that extend this one
        let dependents: Vec<TypeVarID> = self
            .type_var_extensions
            .iter()
            .filter_map(|(tv, exts)| {
                if exts.contains(type_var) {
                    Some(tv.clone())
                } else {
                    None
                }
            })
            .collect();

        for dep in dependents {
            self.invalidate_cache(&dep);
        }
    }

    /// Add an exact row constraint (has exactly these fields)
    fn add_exact_row_constraint(
        &mut self,
        type_var: &TypeVarID,
        row: &RowSpec,
        expr_id: ExprID,
    ) -> Result<(), TypeError> {
        tracing::trace!("add_exact_row_constraint: type_var={:?}", type_var);

        // Check if this type variable already has extensions
        if self.type_var_extensions.contains_key(type_var) {
            return Err(TypeError::Unknown(format!(
                "Cannot add exact row constraint to type variable {type_var:?} which already has extensions",
            )));
        }

        // First add all the fields
        self.add_row_constraint(type_var, row, None, expr_id)?;

        // Mark this type variable as having an exact row
        self.type_var_exact.insert(type_var.clone(), true);

        tracing::trace!("Marked {:?} as exact", type_var);

        Ok(())
    }

    /// Add a lacks constraint
    fn add_lacks_constraint(
        &mut self,
        type_var: &TypeVarID,
        labels: &LabelSet,
    ) -> Result<(), TypeError> {
        // Check if any of the lacking fields are already present
        if let Some(fields) = self.type_var_fields.get(type_var) {
            for label in labels {
                if fields.contains_key(label) {
                    return Err(TypeError::Unknown(format!(
                        "Type variable already has field '{label}' but lacks constraint forbids it"
                    )));
                }
            }
        }

        // Add to lacks set
        self.type_var_lacks
            .entry(type_var.clone())
            .or_default()
            .extend(labels.clone());

        Ok(())
    }

    /// Solve row concatenation constraint
    fn solve_row_concat(
        &mut self,
        left: &TypeVarID,
        right: &TypeVarID,
        result: &TypeVarID,
        _type_subs: &mut Substitutions,
    ) -> Result<(), TypeError> {
        // Build result fields without unnecessary cloning
        let mut result_fields = BTreeMap::new();

        // Add fields from left
        if let Some(left_fields) = self.type_var_fields.get(left) {
            result_fields.extend(left_fields.iter().map(|(k, v)| (k.clone(), v.clone())));
        }

        // Add fields from right (right-biased for conflicts)
        if let Some(right_fields) = self.type_var_fields.get(right) {
            for (label, field) in right_fields {
                if let Some(existing) = result_fields.get(label)
                    && existing.ty != field.ty
                {
                    return Err(TypeError::Unknown(format!(
                        "Field '{label}' has conflicting types in row concatenation"
                    )));
                }
                result_fields.insert(label.clone(), field.clone());
            }
        }

        // Set result fields
        self.type_var_fields.insert(result.clone(), result_fields);

        // Invalidate cache for result
        self.invalidate_cache(result);

        // Concatenate lacks constraints
        let mut result_lacks = LabelSet::new();

        // Add lacks from left
        if let Some(left_lacks) = self.type_var_lacks.get(left) {
            result_lacks.extend(left_lacks.iter().cloned());
        }

        // Add lacks from right
        if let Some(right_lacks) = self.type_var_lacks.get(right) {
            result_lacks.extend(right_lacks.iter().cloned());
        }

        // Remove fields that are present in result
        if let Some(result_fields) = self.type_var_fields.get(result) {
            for label in result_fields.keys() {
                result_lacks.remove(label);
            }
        }

        if !result_lacks.is_empty() {
            self.type_var_lacks.insert(result.clone(), result_lacks);
        }

        // Result of concatenation is NOT exact, even if inputs were exact
        // (concatenation implies the ability to add more fields)
        self.type_var_exact.insert(result.clone(), false);

        Ok(())
    }

    /// Solve row restriction constraint
    fn solve_row_restrict(
        &mut self,
        source: &TypeVarID,
        labels: &LabelSet,
        result: &TypeVarID,
    ) -> Result<(), TypeError> {
        // Build result fields without cloning the entire source map
        let mut result_fields = BTreeMap::new();

        if let Some(source_fields) = self.type_var_fields.get(source) {
            for (label, field) in source_fields {
                if !labels.contains(label) {
                    result_fields.insert(label.clone(), field.clone());
                }
            }
        }

        // Set result fields
        self.type_var_fields.insert(result.clone(), result_fields);

        // Invalidate cache for result
        self.invalidate_cache(result);

        // Update lacks - result lacks everything source lacks plus the restricted labels
        let mut result_lacks = LabelSet::new();

        if let Some(source_lacks) = self.type_var_lacks.get(source) {
            result_lacks.extend(source_lacks.iter().cloned());
        }
        result_lacks.extend(labels.iter().cloned());

        self.type_var_lacks.insert(result.clone(), result_lacks);

        // Inherit exactness from source
        if let Some(&is_exact) = self.type_var_exact.get(source) {
            self.type_var_exact.insert(result.clone(), is_exact);
        }

        Ok(())
    }

    /// Get the resolved fields for a type variable (without extensions)
    pub fn get_resolved_fields(&self, type_var: &TypeVarID) -> Option<&BTreeMap<Label, FieldInfo>> {
        self.type_var_fields.get(type_var)
    }

    /// Get all fields for a type variable including extensions
    pub fn get_all_fields(
        &mut self,
        type_var: &TypeVarID,
    ) -> Result<BTreeMap<Label, FieldInfo>, TypeError> {
        // Check cache first
        if let Some(cached) = self.all_fields_cache.get(type_var) {
            return Ok(cached.clone());
        }

        let mut visited = HashSet::new();
        let result = self.get_all_fields_impl(type_var, &mut visited)?;

        // Cache the result
        self.all_fields_cache
            .insert(type_var.clone(), result.clone());
        Ok(result)
    }

    /// Internal implementation with cycle detection
    fn get_all_fields_impl(
        &self,
        type_var: &TypeVarID,
        visited: &mut HashSet<TypeVarID>,
    ) -> Result<BTreeMap<Label, FieldInfo>, TypeError> {
        // Check for cycles
        if !visited.insert(type_var.clone()) {
            return Err(TypeError::Unknown(format!(
                "Cycle detected in row extensions for type variable {type_var:?}",
            )));
        }

        let mut all_fields = BTreeMap::new();

        // Collect fields from extensions first
        if let Some(extensions) = self.type_var_extensions.get(type_var) {
            for ext in extensions {
                let ext_fields = self.get_all_fields_impl(ext, visited)?;
                for (label, field) in ext_fields {
                    all_fields.insert(label, field);
                }
            }
        }

        // Then add direct fields - check for conflicts
        if let Some(fields) = self.type_var_fields.get(type_var) {
            for (label, field) in fields {
                if let Some(existing) = all_fields.get(label) {
                    // Check if the types are compatible
                    if existing.ty != field.ty {
                        return Err(TypeError::Unknown(format!(
                            "Field '{}' has conflicting types: {:?} from extension vs {:?} from direct definition",
                            label, existing.ty, field.ty
                        )));
                    }
                }
                all_fields.insert(label.clone(), field.clone());
            }
        }

        // Remove from visited set when returning (allows diamond patterns)
        visited.remove(type_var);

        Ok(all_fields)
    }

    /// Check if a type variable has a specific field
    pub fn has_field(&self, type_var: &TypeVarID, label: &Label) -> Option<&FieldInfo> {
        let mut visited = HashSet::new();
        self.has_field_impl(type_var, label, &mut visited)
    }

    /// Internal implementation with cycle detection
    fn has_field_impl(
        &self,
        type_var: &TypeVarID,
        label: &Label,
        visited: &mut HashSet<TypeVarID>,
    ) -> Option<&FieldInfo> {
        // Check for cycles
        if !visited.insert(type_var.clone()) {
            tracing::warn!(
                "Cycle detected in row extensions while looking for field '{}' in type variable {:?}",
                label,
                type_var
            );
            return None;
        }

        // First check direct fields
        if let Some(fields) = self.type_var_fields.get(type_var)
            && let Some(field) = fields.get(label)
        {
            visited.remove(type_var);
            return Some(field);
        }

        // Then check extensions
        if let Some(extensions) = self.type_var_extensions.get(type_var) {
            for ext in extensions {
                if let Some(field) = self.has_field_impl(ext, label, visited) {
                    visited.remove(type_var);
                    return Some(field);
                }
            }
        }

        visited.remove(type_var);
        None
    }
}

/// Extension trait for integrating row constraints with the main constraint system
pub trait ConstraintExtensions {
    /// Convert to extended constraint
    fn to_extended(self) -> ExtendedConstraint;
}

impl ConstraintExtensions for Constraint {
    fn to_extended(self) -> ExtendedConstraint {
        ExtendedConstraint::Base(self)
    }
}

impl ConstraintExtensions for RowConstraint {
    fn to_extended(self) -> ExtendedConstraint {
        ExtendedConstraint::Row(self)
    }
}

/// Helper to create a type variable with row constraints
pub fn create_row_type_var(
    env: &mut Environment,
    constraints: Vec<RowConstraint>,
) -> (TypeVarID, Vec<ExtendedConstraint>) {
    let tv = env.new_type_variable(TypeVarKind::Blank, ExprID(0));
    let extended: Vec<_> = constraints
        .into_iter()
        .map(ExtendedConstraint::Row)
        .collect();
    (tv, extended)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::row::FieldMetadata;

    #[test]
    fn test_field_constraint() {
        let mut env = Environment::new();
        let mut solver = RowConstraintSolver::new(&mut env, 0);
        let mut type_subs = Substitutions::new();

        let tv = TypeVarID::new(0, TypeVarKind::Blank, ExprID(0));
        let constraint = RowConstraint::HasField {
            type_var: tv.clone(),
            label: "x".to_string(),
            field_ty: Ty::Int,
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };

        solver
            .solve_row_constraint(&constraint, ExprID(0), &mut type_subs)
            .unwrap();

        assert!(solver.has_field(&tv, &"x".to_string()).is_some());
    }

    #[test]
    fn test_lacks_constraint() {
        let mut env = Environment::new();
        let mut solver = RowConstraintSolver::new(&mut env, 0);
        let mut type_subs = Substitutions::new();

        let tv = TypeVarID::new(0, TypeVarKind::Blank, ExprID(0));
        let mut labels = LabelSet::new();
        labels.insert("x".to_string());

        let constraint = RowConstraint::Lacks {
            type_var: tv.clone(),
            labels: labels.clone(),
        };

        solver
            .solve_row_constraint(&constraint, ExprID(0), &mut type_subs)
            .unwrap();

        // Now trying to add field x should fail
        let field_constraint = RowConstraint::HasField {
            type_var: tv,
            label: "x".to_string(),
            field_ty: Ty::Int,
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };

        assert!(
            solver
                .solve_row_constraint(&field_constraint, ExprID(0), &mut type_subs)
                .is_err()
        );
    }
}
