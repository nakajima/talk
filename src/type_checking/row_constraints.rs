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
    /// Generation counter for fresh variables
    #[allow(dead_code)]
    generation: u32,
}

impl<'a> RowConstraintSolver<'a> {
    pub fn new(env: &'a mut Environment, generation: u32) -> Self {
        Self {
            env,
            type_var_fields: HashMap::new(),
            type_var_lacks: HashMap::new(),
            generation,
        }
    }

    /// Main entry point for solving a row constraint
    pub fn solve_row_constraint(
        &mut self,
        constraint: &RowConstraint,
        type_subs: &mut Substitutions,
    ) -> Result<(), TypeError> {
        match constraint {
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
        }
    }

    /// Add a field constraint to a type variable
    fn add_field_constraint(
        &mut self,
        type_var: &TypeVarID,
        label: &Label,
        field_ty: &Ty,
        metadata: &crate::row::FieldMetadata,
    ) -> Result<(), TypeError> {
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
        if let Some(_ext) = extension {
            // TODO: Track that type_var can have additional fields from ext
        }

        Ok(())
    }

    /// Add an exact row constraint (has exactly these fields)
    fn add_exact_row_constraint(
        &mut self,
        type_var: &TypeVarID,
        row: &RowSpec,
    ) -> Result<(), TypeError> {
        // First add all the fields
        self.add_row_constraint(type_var, row, None)?;

        // Then mark that no other fields are allowed
        // This is done by recording the exact field set
        // TODO: Implement exact row tracking

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

        Ok(())
    }

    /// Get the resolved fields for a type variable
    pub fn get_resolved_fields(&self, type_var: &TypeVarID) -> Option<&BTreeMap<Label, FieldInfo>> {
        self.type_var_fields.get(type_var)
    }

    /// Check if a type variable has a specific field
    pub fn has_field(&self, type_var: &TypeVarID, label: &Label) -> Option<&FieldInfo> {
        self.type_var_fields
            .get(type_var)
            .and_then(|fields| fields.get(label))
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