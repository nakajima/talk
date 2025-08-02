//! Utilities for working with row constraints and extracting field information
//! This module provides the bridge between the constraint-based row system
//! and code that needs to access field information.

use std::collections::BTreeMap;

use crate::{
    row::{FieldInfo, Label, RowConstraint, RowSpec},
    type_var_id::TypeVarID,
    ty::Ty,
};

/// Context for resolving row constraints to field information
pub struct RowContext<'a> {
    /// All row constraints in the system
    pub constraints: &'a [RowConstraint],
}

impl<'a> RowContext<'a> {
    pub fn new(constraints: &'a [RowConstraint]) -> Self {
        Self { constraints }
    }

    /// Get all fields for a type variable by examining row constraints
    pub fn get_fields_for_type_var(&self, type_var: &TypeVarID) -> BTreeMap<Label, FieldInfo> {
        let mut fields = BTreeMap::new();

        for constraint in self.constraints {
            match constraint {
                RowConstraint::HasField {
                    type_var: tv,
                    label,
                    field_ty,
                    metadata,
                } if tv == type_var => {
                    fields.insert(
                        label.clone(),
                        FieldInfo {
                            ty: field_ty.clone(),
                            expr_id: crate::parsing::expr_id::ExprID(0), // TODO: proper expr_id
                            metadata: metadata.clone(),
                        },
                    );
                }
                RowConstraint::HasRow {
                    type_var: tv,
                    row,
                    ..
                } if tv == type_var => {
                    // Add all fields from the row spec
                    for (label, field_info) in &row.fields {
                        fields.insert(label.clone(), field_info.clone());
                    }
                }
                RowConstraint::HasExactRow {
                    type_var: tv,
                    row,
                } if tv == type_var => {
                    // For exact rows, these are all the fields
                    for (label, field_info) in &row.fields {
                        fields.insert(label.clone(), field_info.clone());
                    }
                }
                _ => {}
            }
        }

        fields
    }

    /// Check if a type variable has a specific field
    pub fn has_field(&self, type_var: &TypeVarID, label: &str) -> bool {
        for constraint in self.constraints {
            match constraint {
                RowConstraint::HasField {
                    type_var: tv,
                    label: field_label,
                    ..
                } if tv == type_var && field_label == label => {
                    return true;
                }
                RowConstraint::HasRow {
                    type_var: tv,
                    row,
                    ..
                } if tv == type_var => {
                    if row.fields.contains_key(label) {
                        return true;
                    }
                }
                RowConstraint::HasExactRow {
                    type_var: tv,
                    row,
                } if tv == type_var => {
                    if row.fields.contains_key(label) {
                        return true;
                    }
                }
                RowConstraint::Lacks {
                    type_var: tv,
                    labels,
                } if tv == type_var => {
                    if labels.contains(label) {
                        return false; // Explicitly lacks this field
                    }
                }
                _ => {}
            }
        }

        false
    }

    /// Get the type of a specific field for a type variable
    pub fn get_field_type(&self, type_var: &TypeVarID, label: &str) -> Option<Ty> {
        for constraint in self.constraints {
            match constraint {
                RowConstraint::HasField {
                    type_var: tv,
                    label: field_label,
                    field_ty,
                    ..
                } if tv == type_var && field_label == label => {
                    return Some(field_ty.clone());
                }
                RowConstraint::HasRow {
                    type_var: tv,
                    row,
                    ..
                } if tv == type_var => {
                    if let Some(field_info) = row.fields.get(label) {
                        return Some(field_info.ty.clone());
                    }
                }
                RowConstraint::HasExactRow {
                    type_var: tv,
                    row,
                } if tv == type_var => {
                    if let Some(field_info) = row.fields.get(label) {
                        return Some(field_info.ty.clone());
                    }
                }
                _ => {}
            }
        }

        None
    }

    /// Check if a type variable represents an exact (closed) row
    pub fn is_exact_row(&self, type_var: &TypeVarID) -> bool {
        for constraint in self.constraints {
            if let RowConstraint::HasExactRow { type_var: tv, .. } = constraint {
                if tv == type_var {
                    return true;
                }
            }
        }
        false
    }

    /// Get the extension variable for an open row
    pub fn get_extension(&self, type_var: &TypeVarID) -> Option<TypeVarID> {
        for constraint in self.constraints {
            if let RowConstraint::HasRow {
                type_var: tv,
                extension,
                ..
            } = constraint
            {
                if tv == type_var {
                    return extension.clone();
                }
            }
        }
        None
    }
}

/// Helper to get fields from a Row type
pub fn get_row_fields(ty: &Ty, constraints: &[RowConstraint]) -> BTreeMap<Label, FieldInfo> {
    match ty {
        Ty::Row { type_var, .. } => {
            let context = RowContext::new(constraints);
            context.get_fields_for_type_var(type_var)
        }
        _ => BTreeMap::new(),
    }
}

/// Helper to check if a Row type has a specific field
pub fn row_has_field(ty: &Ty, label: &str, constraints: &[RowConstraint]) -> bool {
    match ty {
        Ty::Row { type_var, .. } => {
            let context = RowContext::new(constraints);
            context.has_field(type_var, label)
        }
        _ => false,
    }
}

/// Helper to get the type of a specific field in a Row type
pub fn get_row_field_type(ty: &Ty, label: &str, constraints: &[RowConstraint]) -> Option<Ty> {
    match ty {
        Ty::Row { type_var, .. } => {
            let context = RowContext::new(constraints);
            context.get_field_type(type_var, label)
        }
        _ => None,
    }
}