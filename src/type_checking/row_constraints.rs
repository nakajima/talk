//! Row constraint solving for the qualified types system.
//! 
//! This module integrates row constraints into the main constraint solver,
//! treating row structure as qualifications on type variables.

use std::collections::{HashMap, BTreeMap};

use crate::{
    constraint::Constraint,
    environment::Environment,
    expr_id::ExprID,
    row::{RowConstraint, RowSpec, FieldInfo, Label, LabelSet},
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
    #[allow(dead_code)]
    env: &'a mut Environment,
    /// Tracks which fields each type variable has
    type_var_fields: HashMap<TypeVarID, BTreeMap<Label, FieldInfo>>,
    /// Tracks which fields each type variable lacks
    type_var_lacks: HashMap<TypeVarID, LabelSet>,
    /// Tracks which type variables have exact rows (no additional fields allowed)
    type_var_exact: HashMap<TypeVarID, bool>,
    /// All row constraints being processed (for exactness checking)
    all_constraints: Vec<RowConstraint>,
    /// Generation counter for fresh variables
    #[allow(dead_code)]
    generation: u32,
    /// Tracks which type variables extend other type variables
    type_var_extensions: HashMap<TypeVarID, Vec<TypeVarID>>,
}

impl<'a> RowConstraintSolver<'a> {
    pub fn new(env: &'a mut Environment, generation: u32) -> Self {
        Self {
            env,
            type_var_fields: HashMap::new(),
            type_var_lacks: HashMap::new(),
            type_var_exact: HashMap::new(),
            all_constraints: Vec::new(),
            generation,
            type_var_extensions: HashMap::new(),
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
        type_subs: &mut Substitutions,
    ) -> Result<(), TypeError> {
        tracing::trace!("solve_row_constraint: {:?}", constraint);
        let result = match constraint {
            RowConstraint::HasField { type_var, label, field_ty, metadata } => {
                self.add_field_constraint(type_var, label, field_ty, metadata)
            }
            
            RowConstraint::HasRow { type_var, row, extension } => {
                self.add_row_constraint(type_var, row, extension.as_ref())
            }
            
            RowConstraint::HasExactRow { type_var, row } => {
                self.add_exact_row_constraint(type_var, row)
            }
            
            RowConstraint::Lacks { type_var, labels } => {
                self.add_lacks_constraint(type_var, labels)
            }
            
            RowConstraint::RowConcat { left, right, result } => {
                self.solve_row_concat(left, right, result, type_subs)
            }
            
            RowConstraint::RowRestrict { source, labels, result } => {
                self.solve_row_restrict(source, labels, result)
            }
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
    ) -> Result<(), TypeError> {
        tracing::trace!("add_field_constraint: type_var={:?}, label={}, exact={:?}", 
                       type_var, label, self.type_var_exact.get(type_var));
        
        // Check if this type variable has an exact row constraint
        // First check our local state
        let mut is_exact = self.type_var_exact.get(type_var).copied().unwrap_or(false);
        
        // Also check if there's a HasExactRow constraint in all_constraints
        if !is_exact {
            is_exact = self.all_constraints.iter().any(|c| {
                matches!(c, RowConstraint::HasExactRow { type_var: tv, .. } if tv == type_var)
            });
        }
        
        // Types with extensions cannot be exact
        if is_exact && self.type_var_extensions.contains_key(type_var) {
            is_exact = false;
        }
        
        if is_exact {
            // Check if the field already exists or is part of the exact row definition
            let field_allowed = self.type_var_fields.get(type_var)
                .map(|fields| fields.contains_key(label))
                .unwrap_or(false) ||
                self.all_constraints.iter().any(|c| {
                    match c {
                        RowConstraint::HasExactRow { type_var: tv, row } if tv == type_var => {
                            row.fields.contains_key(label)
                        }
                        _ => false,
                    }
                });
                
            if !field_allowed {
                tracing::trace!("Rejecting field '{}' due to exact row constraint", label);
                return Err(TypeError::Unknown(format!(
                    "Cannot add field '{}' to type with exact row constraint",
                    label
                )));
            }
        }
        
        // Check lacks constraints
        if let Some(lacks) = self.type_var_lacks.get(type_var) {
            if lacks.contains(label) {
                return Err(TypeError::Unknown(format!(
                    "Type variable cannot have field '{}' due to lacks constraint",
                    label
                )));
            }
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
            fields.insert(label.clone(), FieldInfo {
                ty: field_ty.clone(),
                expr_id: ExprID(0), // TODO: proper expr_id
                metadata: metadata.clone(),
            });
        }

        Ok(())
    }

    /// Add a row constraint (has at least these fields)
    fn add_row_constraint(
        &mut self,
        type_var: &TypeVarID,
        row: &RowSpec,
        extension: Option<&TypeVarID>,
    ) -> Result<(), TypeError> {
        // Add all fields from the row
        for (label, field) in &row.fields {
            self.add_field_constraint(type_var, label, &field.ty, &field.metadata)?;
        }

        // If there's an extension, record that relationship
        if let Some(ext) = extension {
            // Track that type_var is extended by ext
            self.type_var_extensions
                .entry(type_var.clone())
                .or_default()
                .push(ext.clone());
        }

        Ok(())
    }

    /// Add an exact row constraint (has exactly these fields)
    fn add_exact_row_constraint(
        &mut self,
        type_var: &TypeVarID,
        row: &RowSpec,
    ) -> Result<(), TypeError> {
        tracing::trace!("add_exact_row_constraint: type_var={:?}", type_var);
        
        // First add all the fields
        self.add_row_constraint(type_var, row, None)?;

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
                        "Type variable already has field '{}' but lacks constraint forbids it",
                        label
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
        // Get fields from left and right
        let left_fields = self.type_var_fields.get(left).cloned().unwrap_or_default();
        let right_fields = self.type_var_fields.get(right).cloned().unwrap_or_default();

        // Concatenate (right-biased for conflicts)
        let mut result_fields = left_fields;
        for (label, field) in right_fields {
            if let Some(existing) = result_fields.get(&label) {
                if existing.ty != field.ty {
                    return Err(TypeError::Unknown(format!(
                        "Field '{}' has conflicting types in row concatenation",
                        label
                    )));
                }
            }
            result_fields.insert(label, field);
        }

        // Set result fields
        self.type_var_fields.insert(result.clone(), result_fields);

        // Concatenate lacks constraints
        let left_lacks = self.type_var_lacks.get(left).cloned().unwrap_or_default();
        let right_lacks = self.type_var_lacks.get(right).cloned().unwrap_or_default();
        
        // Result lacks = (left_lacks ∪ right_lacks) - result_fields
        let mut result_lacks = left_lacks;
        result_lacks.extend(right_lacks);
        for label in self.type_var_fields.get(result).unwrap().keys() {
            result_lacks.remove(label);
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
        // Get source fields
        let source_fields = self.type_var_fields.get(source).cloned().unwrap_or_default();

        // Remove specified labels
        let result_fields: BTreeMap<_, _> = source_fields
            .into_iter()
            .filter(|(label, _)| !labels.contains(label))
            .collect();

        // Set result fields
        self.type_var_fields.insert(result.clone(), result_fields);

        // Update lacks - result lacks everything source lacks plus the restricted labels
        let mut result_lacks = self.type_var_lacks.get(source).cloned().unwrap_or_default();
        result_lacks.extend(labels.clone());
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
    pub fn get_all_fields(&self, type_var: &TypeVarID) -> BTreeMap<Label, FieldInfo> {
        let mut all_fields = BTreeMap::new();
        
        // Collect fields from extensions first (so direct fields can override)
        if let Some(extensions) = self.type_var_extensions.get(type_var) {
            for ext in extensions {
                let ext_fields = self.get_all_fields(ext);
                all_fields.extend(ext_fields);
            }
        }
        
        // Then add direct fields (these take precedence)
        if let Some(fields) = self.type_var_fields.get(type_var) {
            all_fields.extend(fields.clone());
        }
        
        all_fields
    }

    /// Check if a type variable has a specific field
    pub fn has_field(&self, type_var: &TypeVarID, label: &Label) -> Option<&FieldInfo> {
        // First check direct fields
        if let Some(fields) = self.type_var_fields.get(type_var) {
            if let Some(field) = fields.get(label) {
                return Some(field);
            }
        }
        
        // Then check extensions
        if let Some(extensions) = self.type_var_extensions.get(type_var) {
            for ext in extensions {
                if let Some(field) = self.has_field(ext, label) {
                    return Some(field);
                }
            }
        }
        
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
        .map(|c| ExtendedConstraint::Row(c))
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

        solver.solve_row_constraint(&constraint, &mut type_subs).unwrap();
        
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

        solver.solve_row_constraint(&constraint, &mut type_subs).unwrap();

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

        assert!(solver.solve_row_constraint(&field_constraint, &mut type_subs).is_err());
    }
}