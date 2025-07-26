//! Test member resolution for row-based type variables

#[cfg(test)]
mod tests {
    use crate::{
        constraint::Constraint,
        environment::Environment,
        expr_id::ExprID,
        row::{RowConstraint, FieldMetadata},
        ty::Ty,
        type_var_id::TypeVarKind,
        ExprMetaStorage,
    };
    
    /// Test that member access works on type variables created through row operations
    #[test]
    fn test_member_access_on_row_concat_result() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create two source type variables with fields
        let left = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Left".to_string()),
            ExprID(1),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(2),
            constraint: RowConstraint::HasField {
                type_var: left.clone(),
                label: "x".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        let right = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Right".to_string()),
            ExprID(3),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(4),
            constraint: RowConstraint::HasField {
                type_var: right.clone(),
                label: "y".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Create result through concatenation
        let result = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Result".to_string()),
            ExprID(5),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(6),
            constraint: RowConstraint::RowConcat {
                left: left.clone(),
                right: right.clone(),
                result: result.clone(),
            },
        });
        
        // First flush to process row constraints
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Now try to access fields on the result
        let x_access = env.new_type_variable(TypeVarKind::Blank, ExprID(10));
        env.constrain(Constraint::MemberAccess(
            ExprID(11),
            Ty::TypeVar(result.clone()),
            "x".to_string(),
            Ty::TypeVar(x_access.clone()),
        ));
        
        let y_access = env.new_type_variable(TypeVarKind::Blank, ExprID(12));
        env.constrain(Constraint::MemberAccess(
            ExprID(13),
            Ty::TypeVar(result.clone()),
            "y".to_string(),
            Ty::TypeVar(y_access.clone()),
        ));
        
        // This should succeed
        let mut solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Verify types
        let x_ty = solution.substitutions.apply(&Ty::TypeVar(x_access), 0, &mut env.context);
        assert_eq!(x_ty, Ty::Int);
        
        let y_ty = solution.substitutions.apply(&Ty::TypeVar(y_access), 0, &mut env.context);
        assert_eq!(y_ty, Ty::Int);
    }
    
    /// Test member access on row-restricted type variables
    #[test]
    fn test_member_access_on_row_restrict_result() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create source with multiple fields
        let source = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Source".to_string()),
            ExprID(20),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(21),
            constraint: RowConstraint::HasField {
                type_var: source.clone(),
                label: "public".to_string(),
                field_ty: Ty::string(),
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
                type_var: source.clone(),
                label: "secret".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Create restricted version
        let restricted = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Restricted".to_string()),
            ExprID(25),
        );
        
        let mut labels = crate::row::LabelSet::new();
        labels.insert("secret".to_string());
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(26),
            constraint: RowConstraint::RowRestrict {
                source: source.clone(),
                labels,
                result: restricted.clone(),
            },
        });
        
        // Access public field (should succeed)
        let public_access = env.new_type_variable(TypeVarKind::Blank, ExprID(30));
        env.constrain(Constraint::MemberAccess(
            ExprID(31),
            Ty::TypeVar(restricted.clone()),
            "public".to_string(),
            Ty::TypeVar(public_access.clone()),
        ));
        
        // Process all constraints together
        let mut solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        let public_ty = solution.substitutions.apply(&Ty::TypeVar(public_access), 0, &mut env.context);
        assert_eq!(public_ty, Ty::string());
        
        // Now test that accessing secret field fails
        // We need to set up the constraints again since we can't reuse the environment after flush
        let mut env2 = Environment::new();
        
        // Recreate source
        let source2 = env2.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Source".to_string()),
            ExprID(40),
        );
        
        env2.constrain(Constraint::Row {
            expr_id: ExprID(41),
            constraint: RowConstraint::HasField {
                type_var: source2.clone(),
                label: "public".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        env2.constrain(Constraint::Row {
            expr_id: ExprID(42),
            constraint: RowConstraint::HasField {
                type_var: source2.clone(),
                label: "secret".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Create restricted
        let restricted2 = env2.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Restricted".to_string()),
            ExprID(45),
        );
        
        let mut labels2 = crate::row::LabelSet::new();
        labels2.insert("secret".to_string());
        
        env2.constrain(Constraint::Row {
            expr_id: ExprID(46),
            constraint: RowConstraint::RowRestrict {
                source: source2,
                labels: labels2,
                result: restricted2.clone(),
            },
        });
        
        // Try to access secret field
        let secret_access = env2.new_type_variable(TypeVarKind::Blank, ExprID(50));
        env2.constrain(Constraint::MemberAccess(
            ExprID(51),
            Ty::TypeVar(restricted2),
            "secret".to_string(),
            Ty::TypeVar(secret_access),
        ));
        
        let solution2 = env2.flush_constraints(&meta).unwrap();
        assert!(!solution2.errors.is_empty());
    }
    
    /// Test that row constraints are resolved before member access
    #[test]
    fn test_constraint_ordering() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a type variable
        let tv = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("HasFields".to_string()),
            ExprID(40),
        );
        
        // Add both member access and row constraint in the same batch
        let field_result = env.new_type_variable(TypeVarKind::Blank, ExprID(41));
        
        // Add member access first
        env.constrain(Constraint::MemberAccess(
            ExprID(42),
            Ty::TypeVar(tv.clone()),
            "field".to_string(),
            Ty::TypeVar(field_result.clone()),
        ));
        
        // Then add the row constraint that defines the field
        env.constrain(Constraint::Row {
            expr_id: ExprID(43),
            constraint: RowConstraint::HasField {
                type_var: tv.clone(),
                label: "field".to_string(),
                field_ty: Ty::Bool,
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Should resolve correctly despite ordering
        let mut solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        let field_ty = solution.substitutions.apply(&Ty::TypeVar(field_result), 0, &mut env.context);
        assert_eq!(field_ty, Ty::Bool);
    }
}