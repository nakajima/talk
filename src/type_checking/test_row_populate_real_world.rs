//! Test real-world scenarios for populate_from_rows

#[cfg(test)]
mod tests {
    use crate::{
        SymbolID,
        constraint::Constraint,
        environment::Environment,
        expr_id::ExprID,
        row::{RowConstraint, FieldMetadata},
        ty::Ty,
        type_def::{TypeDef, TypeDefKind, Method, TypeMember},
        type_var_id::TypeVarKind,
    };
    
    /// Test a scenario where a type is extended through row operations
    #[test]
    fn test_type_extension_scenario() {
        let mut env = Environment::new();
        
        // Create a base User type
        let user_id = SymbolID(8000);
        let mut user_def = TypeDef::new(
            user_id,
            "User".to_string(),
            TypeDefKind::Struct,
            vec![],
        );
        
        // Give it a row variable
        let user_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("UserRow".to_string()),
            ExprID(1),
        );
        user_def.row_var = Some(user_row.clone());
        
        // Add some initial fields via row constraints
        env.constrain(Constraint::Row {
            expr_id: ExprID(2),
            constraint: RowConstraint::HasField {
                type_var: user_row.clone(),
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
            expr_id: ExprID(3),
            constraint: RowConstraint::HasField {
                type_var: user_row.clone(),
                label: "name".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Also manually add a method (simulating imported behavior)
        user_def.members.insert(
            "toString".to_string(),
            TypeMember::Method(Method::new(
                "toString".to_string(),
                ExprID(4),
                Ty::Func(vec![], Box::new(Ty::string()), vec![]),
            )),
        );
        
        env.register(&user_def).unwrap();
        
        // First populate
        user_def.populate_from_rows(&env);
        assert_eq!(user_def.members.len(), 3); // id, name, toString
        
        // Now simulate extending the type (e.g., from a different module)
        // Clear constraints and add new ones
        env.clear_constraints();
        
        // Re-add the base fields plus new ones
        env.constrain(Constraint::Row {
            expr_id: ExprID(5),
            constraint: RowConstraint::HasField {
                type_var: user_row.clone(),
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
            expr_id: ExprID(6),
            constraint: RowConstraint::HasField {
                type_var: user_row.clone(),
                label: "name".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(7),
            constraint: RowConstraint::HasField {
                type_var: user_row.clone(),
                label: "email".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::RecordField {
                    index: 2,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(8),
            constraint: RowConstraint::HasField {
                type_var: user_row.clone(),
                label: "isActive".to_string(),
                field_ty: Ty::Bool,
                metadata: FieldMetadata::RecordField {
                    index: 3,
                    has_default: true,
                    is_mutable: true,
                },
            },
        });
        
        // Re-populate - should update row fields while preserving toString
        user_def.populate_from_rows(&env);
        
        // Should have all fields
        assert_eq!(user_def.members.len(), 5); // id, name, email, isActive, toString
        assert!(user_def.members.contains_key("id"));
        assert!(user_def.members.contains_key("name"));
        assert!(user_def.members.contains_key("email"));
        assert!(user_def.members.contains_key("isActive"));
        assert!(user_def.members.contains_key("toString"));
        
        // Verify toString is still a method
        assert!(matches!(
            user_def.members.get("toString"),
            Some(TypeMember::Method(_))
        ));
        
        // Verify new fields have correct types
        if let Some(TypeMember::Property(email)) = user_def.members.get("email") {
            assert_eq!(email.ty, Ty::string());
        } else {
            panic!("email should be a property");
        }
        
        if let Some(TypeMember::Property(is_active)) = user_def.members.get("isActive") {
            assert_eq!(is_active.ty, Ty::Bool);
            assert!(is_active.has_default);
        } else {
            panic!("isActive should be a property");
        }
    }
}