//! Qualified row types for extensible data types.
//! 
//! This module implements row types using qualified types (constraints on type variables)
//! based on the papers by J. Garrett Morris et al. Row structure is expressed as
//! constraints rather than being embedded directly in types.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::{
    expr_id::ExprID,
    substitutions::Substitutions,
    ty::Ty,
    type_var_id::TypeVarID,
};

/// A label for a field/variant in a row
pub type Label = String;

/// A set of labels (used for row constraints)
pub type LabelSet = BTreeSet<Label>;

/// Row-specific constraints that qualify types
/// These express row structure as constraints on type variables
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RowConstraint {
    /// Type variable has a specific field
    HasField {
        type_var: TypeVarID,
        label: Label,
        field_ty: Ty,
        metadata: FieldMetadata,
    },
    
    /// Type variable has at least these fields (open row)
    HasRow {
        type_var: TypeVarID,
        row: RowSpec,
        /// If Some, the type may have additional unknown fields
        extension: Option<TypeVarID>,
    },
    
    /// Type variable has exactly these fields (closed row)
    HasExactRow {
        type_var: TypeVarID,
        row: RowSpec,
    },
    
    /// Type variable lacks certain fields
    Lacks {
        type_var: TypeVarID,
        labels: LabelSet,
    },
    
    /// Row concatenation: T1 ⊕ T2 = T3
    RowConcat {
        left: TypeVarID,
        right: TypeVarID,
        result: TypeVarID,
    },
    
    /// Row restriction: T1 \ labels = T2  
    RowRestrict {
        source: TypeVarID,
        labels: LabelSet,
        result: TypeVarID,
    },
}

/// Information about a single field/variant
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldInfo {
    /// The type of this field
    pub ty: Ty,
    /// Expression ID where defined
    pub expr_id: ExprID,
    /// Additional metadata
    pub metadata: FieldMetadata,
}

/// Metadata for fields (different for records vs variants)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldMetadata {
    /// Record field metadata (struct property)
    RecordField {
        /// Position index in the struct
        index: usize,
        /// Whether field has a default value
        has_default: bool,
        /// Whether this is a mutable field
        is_mutable: bool,
    },
    /// Variant field (for pattern matching)
    VariantField {
        /// Position in the variant
        position: usize,
    },
    /// Enum case/variant
    EnumCase {
        /// Tag/discriminant value
        tag: usize,
    },
    /// Method on a type
    Method,
    /// Method requirement in a protocol
    MethodRequirement,
    /// Initializer function
    Initializer,
    /// Enum variant
    EnumVariant {
        /// Tag for pattern matching
        tag: usize,
    },
}

/// Row specification used in constraints
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RowSpec {
    /// The fields in this row
    pub fields: BTreeMap<Label, FieldInfo>,
}

impl RowSpec {
    /// Creates a new row specification
    pub fn new(fields: BTreeMap<Label, FieldInfo>) -> Self {
        RowSpec { fields }
    }

    /// Creates an empty row specification
    pub fn empty() -> Self {
        RowSpec {
            fields: BTreeMap::new(),
        }
    }

    /// Adds a field to the row
    pub fn with_field(mut self, label: Label, info: FieldInfo) -> Self {
        self.fields.insert(label, info);
        self
    }

    /// Gets a field by label
    pub fn get_field(&self, label: &Label) -> Option<&FieldInfo> {
        self.fields.get(label)
    }

    /// Checks if this row has a field
    pub fn has_field(&self, label: &Label) -> bool {
        self.fields.contains_key(label)
    }

    /// Apply type substitutions to all field types
    pub fn substitute(&mut self, subs: &Substitutions) {
        for (_, field) in self.fields.iter_mut() {
            field.ty = crate::constraint_solver::ConstraintSolver::substitute_ty_with_map(&field.ty, subs);
        }
    }

    /// Concatenate two row specs
    pub fn concat(&self, other: &RowSpec) -> Result<RowSpec, RowError> {
        let mut fields = self.fields.clone();
        
        for (label, field) in &other.fields {
            if let Some(existing) = self.fields.get(label) {
                // Check compatibility
                if existing.ty != field.ty {
                    return Err(RowError::FieldConflict(label.clone()));
                }
            }
            fields.insert(label.clone(), field.clone());
        }
        
        Ok(RowSpec { fields })
    }

    /// Restrict (remove) fields from the row
    pub fn restrict(&self, labels: &LabelSet) -> RowSpec {
        let fields = self.fields
            .iter()
            .filter(|(label, _)| !labels.contains(*label))
            .map(|(l, f)| (l.clone(), f.clone()))
            .collect();
        
        RowSpec { fields }
    }
}

/// Errors that can occur during row operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RowError {
    /// Field conflict during concatenation
    FieldConflict(Label),
    /// Missing required field
    MissingField(Label),
    /// Lacks constraint violation
    LacksViolation(Label),
    /// Invalid row operation
    InvalidOperation(String),
}

impl fmt::Display for RowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RowError::FieldConflict(label) => {
                write!(f, "Conflicting definitions for field '{}'", label)
            }
            RowError::MissingField(label) => {
                write!(f, "Missing required field '{}'", label)
            }
            RowError::LacksViolation(label) => {
                write!(f, "Row variable cannot have field '{}'", label)
            }
            RowError::InvalidOperation(msg) => {
                write!(f, "Invalid row operation: {}", msg)
            }
        }
    }
}

/// Helper to check if a type variable has row constraints
pub fn get_row_constraints<'a>(
    type_var: &TypeVarID,
    constraints: &'a [RowConstraint],
) -> Vec<&'a RowConstraint> {
    constraints
        .iter()
        .filter(|c| match c {
            RowConstraint::HasField { type_var: tv, .. } => tv == type_var,
            RowConstraint::HasRow { type_var: tv, .. } => tv == type_var,
            RowConstraint::HasExactRow { type_var: tv, .. } => tv == type_var,
            RowConstraint::Lacks { type_var: tv, .. } => tv == type_var,
            _ => false,
        })
        .collect()
}

/// Check if a type variable has a specific field based on constraints
pub fn has_field_constraint<'a>(
    type_var: &TypeVarID,
    label: &Label,
    constraints: &'a [RowConstraint],
) -> Option<&'a Ty> {
    for constraint in constraints {
        match constraint {
            RowConstraint::HasField {
                type_var: tv,
                label: l,
                field_ty,
                ..
            } if tv == type_var && l == label => {
                return Some(field_ty);
            }
            RowConstraint::HasRow { type_var: tv, row, .. }
            | RowConstraint::HasExactRow { type_var: tv, row }
                if tv == type_var => {
                if let Some(field) = row.get_field(label) {
                    return Some(&field.ty);
                }
            }
            _ => {}
        }
    }
    None
}

/// Builder for creating row constraints
pub struct RowConstraintBuilder {
    constraints: Vec<RowConstraint>,
}

impl RowConstraintBuilder {
    pub fn new() -> Self {
        RowConstraintBuilder {
            constraints: Vec::new(),
        }
    }

    pub fn has_field(
        mut self,
        type_var: TypeVarID,
        label: Label,
        field_ty: Ty,
        metadata: FieldMetadata,
    ) -> Self {
        self.constraints.push(RowConstraint::HasField {
            type_var,
            label,
            field_ty,
            metadata,
        });
        self
    }

    pub fn has_row(
        mut self,
        type_var: TypeVarID,
        row: RowSpec,
        extension: Option<TypeVarID>,
    ) -> Self {
        self.constraints.push(RowConstraint::HasRow {
            type_var,
            row,
            extension,
        });
        self
    }

    pub fn has_exact_row(mut self, type_var: TypeVarID, row: RowSpec) -> Self {
        self.constraints.push(RowConstraint::HasExactRow { type_var, row });
        self
    }

    pub fn lacks(mut self, type_var: TypeVarID, labels: LabelSet) -> Self {
        self.constraints.push(RowConstraint::Lacks { type_var, labels });
        self
    }

    pub fn build(self) -> Vec<RowConstraint> {
        self.constraints
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_row_spec_operations() {
        let row1 = RowSpec::empty()
            .with_field(
                "x".to_string(),
                FieldInfo {
                    ty: Ty::Int,
                    expr_id: ExprID(0),
                    metadata: FieldMetadata::RecordField {
                        index: 0,
                        has_default: false,
                        is_mutable: false,
                    },
                },
            );

        let row2 = RowSpec::empty()
            .with_field(
                "y".to_string(),
                FieldInfo {
                    ty: Ty::Float,
                    expr_id: ExprID(1),
                    metadata: FieldMetadata::RecordField {
                        index: 1,
                        has_default: false,
                        is_mutable: false,
                    },
                },
            );

        // Test concatenation
        let combined = row1.concat(&row2).unwrap();
        assert_eq!(combined.fields.len(), 2);
        assert!(combined.has_field(&"x".to_string()));
        assert!(combined.has_field(&"y".to_string()));

        // Test restriction
        let mut labels = LabelSet::new();
        labels.insert("x".to_string());
        let restricted = combined.restrict(&labels);
        assert_eq!(restricted.fields.len(), 1);
        assert!(!restricted.has_field(&"x".to_string()));
        assert!(restricted.has_field(&"y".to_string()));
    }

    #[test]
    fn test_row_constraints() {
        use crate::type_var_id::TypeVarKind;
        let tv = TypeVarID::new(0, TypeVarKind::Blank, ExprID(0));
        
        let constraints = RowConstraintBuilder::new()
            .has_field(
                tv.clone(),
                "x".to_string(),
                Ty::Int,
                FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            )
            .build();

        assert_eq!(
            has_field_constraint(&tv, &"x".to_string(), &constraints),
            Some(&Ty::Int)
        );
        assert_eq!(
            has_field_constraint(&tv, &"y".to_string(), &constraints),
            None
        );
    }
}