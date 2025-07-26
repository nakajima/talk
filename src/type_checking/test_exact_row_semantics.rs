//! Test exact row semantics for closed types

#[cfg(test)]
mod tests {
    use crate::{
        constraint::Constraint,
        environment::Environment,
        expr_id::ExprID,
        row::{RowConstraint, FieldMetadata, RowSpec, FieldInfo},
        ty::Ty,
        type_var_id::TypeVarKind,
        ExprMetaStorage,
    };
    use std::collections::BTreeMap;
    
    /// Test that HasExactRow prevents additional fields
    #[test]
    fn test_exact_row_prevents_additional_fields() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a type variable with an exact row
        let exact_point = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("ExactPoint".to_string()),
            ExprID(1),
        );
        
        // Define exact row with x and y
        let mut fields = BTreeMap::new();
        fields.insert(
            "x".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(2),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        fields.insert(
            "y".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(3),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        let exact_row = RowSpec { fields };
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(4),
            constraint: RowConstraint::HasExactRow {
                type_var: exact_point.clone(),
                row: exact_row,
            },
        });
        
        // Try to add an additional field (should fail)
        env.constrain(Constraint::Row {
            expr_id: ExprID(5),
            constraint: RowConstraint::HasField {
                type_var: exact_point.clone(),
                label: "z".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 2,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(!solution.errors.is_empty(), "Adding field to exact row should fail");
    }
    
    /// Test that HasRow allows additional fields
    #[test]
    fn test_has_row_allows_additional_fields() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a type variable with an open row
        let open_point = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("OpenPoint".to_string()),
            ExprID(10),
        );
        
        // Define row with x and y
        let mut fields = BTreeMap::new();
        fields.insert(
            "x".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(11),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        fields.insert(
            "y".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(12),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        let open_row = RowSpec { fields };
        let extension_var = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Extension".to_string()),
            ExprID(13),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(14),
            constraint: RowConstraint::HasRow {
                type_var: open_point.clone(),
                row: open_row,
                extension: Some(extension_var),
            },
        });
        
        // This should succeed
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Try to add an additional field (should succeed)
        env.constrain(Constraint::Row {
            expr_id: ExprID(15),
            constraint: RowConstraint::HasField {
                type_var: open_point.clone(),
                label: "z".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 2,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty(), "Adding field to open row should succeed");
    }
    
    /// Test exact row with row operations
    #[test]
    fn test_exact_row_with_operations() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create source types
        let base = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Base".to_string()),
            ExprID(20),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(21),
            constraint: RowConstraint::HasField {
                type_var: base.clone(),
                label: "id".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(22),
            constraint: RowConstraint::HasField {
                type_var: base.clone(),
                label: "name".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Create exact type from base
        let exact_type = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("ExactType".to_string()),
            ExprID(25),
        );
        
        // Create exact row from base fields
        let mut exact_fields = BTreeMap::new();
        exact_fields.insert(
            "id".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(26),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        exact_fields.insert(
            "name".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(27),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(28),
            constraint: RowConstraint::HasExactRow {
                type_var: exact_type.clone(),
                row: RowSpec { fields: exact_fields },
            },
        });
        
        // Trying to add a field to exact type should fail
        env.constrain(Constraint::Row {
            expr_id: ExprID(29),
            constraint: RowConstraint::HasField {
                type_var: exact_type,
                label: "extra".to_string(),
                field_ty: Ty::Bool,
                metadata: FieldMetadata::RecordField {
                    index: 2,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(!solution.errors.is_empty(), "Cannot add fields to exact row");
    }
}