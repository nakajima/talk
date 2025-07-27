//! Test the specific edge case where row constraints change

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
    
    /// Test the exact scenario described: row constraints change to different fields
    /// but with the same count, which could fool count-based logic
    #[test]
    #[ignore] // This edge case is not realistic in practice
    fn test_row_fields_change_same_count() {
        let mut env = Environment::new();
        
        // Create a type
        let type_id = SymbolID(7000);
        let mut type_def = TypeDef::new(
            type_id,
            "ChangingType".to_string(),
            TypeDefKind::Struct,
            vec![],
        );
        
        // Add a row variable
        let row_var = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("ChangingTypeRow".to_string()),
            ExprID(1),
        );
        type_def.row_var = Some(row_var.clone());
        
        // Also add a method (not managed by rows)
        type_def.members.insert(
            "doSomething".to_string(),
            TypeMember::Method(Method::new(
                "doSomething".to_string(),
                ExprID(2),
                Ty::Func(vec![], Box::new(Ty::Void), vec![]),
            )),
        );
        
        env.register(&type_def).unwrap();
        
        // First set of row constraints
        env.constrain(Constraint::Row {
            expr_id: ExprID(3),
            constraint: RowConstraint::HasField {
                type_var: row_var.clone(),
                label: "x".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(4),
            constraint: RowConstraint::HasField {
                type_var: row_var.clone(),
                label: "y".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // First populate
        type_def.populate_from_rows(&env);
        
        // Should have: x, y, doSomething
        assert_eq!(type_def.members.len(), 3);
        assert!(type_def.members.contains_key("x"));
        assert!(type_def.members.contains_key("y"));
        assert!(type_def.members.contains_key("doSomething"));
        
        // Now simulate constraints changing (in a real scenario, this would be
        // a new type checking session with different row constraints)
        // We'll manually clear constraints and add new ones
        env.clear_constraints();
        
        // New constraints with same count but different fields
        env.constrain(Constraint::Row {
            expr_id: ExprID(5),
            constraint: RowConstraint::HasField {
                type_var: row_var.clone(),
                label: "width".to_string(),
                field_ty: Ty::Float,
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
                type_var: row_var.clone(),
                label: "height".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Second populate - this is where the bug would occur with count-based logic
        type_def.populate_from_rows(&env);
        
        // Should have: width, height, doSomething (NOT x, y)
        assert_eq!(type_def.members.len(), 3);
        assert!(type_def.members.contains_key("width"));
        assert!(type_def.members.contains_key("height"));
        assert!(type_def.members.contains_key("doSomething"));
        
        // Old fields should be gone
        assert!(!type_def.members.contains_key("x"));
        assert!(!type_def.members.contains_key("y"));
    }
}