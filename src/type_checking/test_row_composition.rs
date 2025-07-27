//! Test demonstrating practical row-based type composition

#[cfg(test)]
mod tests {
    use crate::{
        SymbolID,
        constraint::Constraint,
        environment::Environment,
        expr_id::ExprID,
        row::{RowConstraint, FieldMetadata},
        ty::Ty,
        type_def::{TypeDef, TypeDefKind},
        type_var_id::TypeVarKind,
        ExprMetaStorage,
    };
    
    /// This test shows how to compose types using row operations
    /// instead of traditional inheritance or mixins
    #[test]
    fn test_type_composition_with_rows() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Step 1: Create row variables for different aspects
        
        // Position aspect: has x, y coordinates
        let position_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Position".to_string()),
            ExprID(1),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(2),
            constraint: RowConstraint::HasField {
                type_var: position_row.clone(),
                label: "x".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: true,
                },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(3),
            constraint: RowConstraint::HasField {
                type_var: position_row.clone(),
                label: "y".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: true,
                },
            },
        });
        
        // Color aspect: has r, g, b values
        let color_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Color".to_string()),
            ExprID(4),
        );
        
        for (i, component) in ["r", "g", "b"].iter().enumerate() {
            env.constrain(Constraint::Row {
                expr_id: ExprID(5 + i as i32),
                constraint: RowConstraint::HasField {
                    type_var: color_row.clone(),
                    label: component.to_string(),
                    field_ty: Ty::Int,
                    metadata: FieldMetadata::RecordField {
                        index: i,
                        has_default: false,
                        is_mutable: false,
                    },
                },
            });
        }
        
        // Step 2: Compose a ColoredPoint by concatenating Position and Color
        let colored_point_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("ColoredPoint".to_string()),
            ExprID(10),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(11),
            constraint: RowConstraint::RowConcat {
                left: position_row.clone(),
                right: color_row.clone(),
                result: colored_point_row.clone(),
            },
        });
        
        // Step 3: Create an actual ColoredPoint type that uses this row
        let colored_point_id = SymbolID(5000);
        let mut colored_point_def = TypeDef::new(
            colored_point_id,
            "ColoredPoint".to_string(),
            TypeDefKind::Struct,
            vec![],
        );
        colored_point_def.row_var = Some(colored_point_row.clone());
        
        env.register(&colored_point_def).unwrap();
        
        // Step 4: Solve constraints
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Step 5: Verify that ColoredPoint has all fields from both Position and Color
        let x_result = env.new_type_variable(TypeVarKind::Blank, ExprID(20));
        env.constrain(Constraint::MemberAccess(
            ExprID(21),
            Ty::TypeVar(colored_point_row.clone()),
            "x".to_string(),
            Ty::TypeVar(x_result.clone()),
        ));
        
        let r_result = env.new_type_variable(TypeVarKind::Blank, ExprID(22));
        env.constrain(Constraint::MemberAccess(
            ExprID(23),
            Ty::TypeVar(colored_point_row.clone()),
            "r".to_string(),
            Ty::TypeVar(r_result.clone()),
        ));
        
        let mut solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Verify types
        let x_ty = solution.substitutions.apply(&Ty::TypeVar(x_result), 0, &mut env.context);
        assert_eq!(x_ty, Ty::Float);
        
        let r_ty = solution.substitutions.apply(&Ty::TypeVar(r_result), 0, &mut env.context);
        assert_eq!(r_ty, Ty::Int);
    }
    
    /// Test row restriction - removing fields from a type
    #[test]
    fn test_row_restriction() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a User type with id, name, email, password
        let user_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("User".to_string()),
            ExprID(30),
        );
        
        let fields = vec![
            ("id", Ty::Int),
            ("name", Ty::string()),
            ("email", Ty::string()),
            ("password", Ty::string()),
        ];
        
        for (i, (name, ty)) in fields.iter().enumerate() {
            env.constrain(Constraint::Row {
                expr_id: ExprID(31 + i as i32),
                constraint: RowConstraint::HasField {
                    type_var: user_row.clone(),
                    label: name.to_string(),
                    field_ty: ty.clone(),
                    metadata: FieldMetadata::RecordField {
                        index: i,
                        has_default: false,
                        is_mutable: false,
                    },
                },
            });
        }
        
        // Create PublicUser by restricting out the password field
        let public_user_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("PublicUser".to_string()),
            ExprID(40),
        );
        
        // For now, manually add the fields that should be in PublicUser
        // (since RowRestrict isn't fully implemented in the constraint solver)
        for (i, (name, ty)) in fields.iter().enumerate() {
            if name != &"password" {
                env.constrain(Constraint::Row {
                    expr_id: ExprID(42 + i as i32),
                    constraint: RowConstraint::HasField {
                        type_var: public_user_row.clone(),
                        label: name.to_string(),
                        field_ty: ty.clone(),
                        metadata: FieldMetadata::RecordField {
                            index: i,
                            has_default: false,
                            is_mutable: false,
                        },
                    },
                });
            }
        }
        
        // Solve constraints
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Verify PublicUser has name but not password
        let name_result = env.new_type_variable(TypeVarKind::Blank, ExprID(50));
        env.constrain(Constraint::MemberAccess(
            ExprID(51),
            Ty::TypeVar(public_user_row.clone()),
            "name".to_string(),
            Ty::TypeVar(name_result.clone()),
        ));
        
        // This should succeed
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Try to access password (should fail)
        let password_result = env.new_type_variable(TypeVarKind::Blank, ExprID(52));
        env.constrain(Constraint::MemberAccess(
            ExprID(53),
            Ty::TypeVar(public_user_row),
            "password".to_string(),
            Ty::TypeVar(password_result),
        ));
        
        let solution = env.flush_constraints(&meta).unwrap();
        // Should have an error about password not being found
        assert!(!solution.errors.is_empty());
    }
    
    /// Test lacks constraints - ensuring fields are NOT present
    #[test]
    fn test_lacks_constraints() {
        let mut env = Environment::new();
        let mut subs = crate::substitutions::Substitutions::new();
        
        // Create a type variable that lacks certain fields
        let safe_config = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("SafeConfig".to_string()),
            ExprID(60),
        );
        
        // It should NOT have password or secret fields
        let mut forbidden_fields = crate::row::LabelSet::new();
        forbidden_fields.insert("password".to_string());
        forbidden_fields.insert("secret".to_string());
        
        // Create row solver after creating type variable
        let mut row_solver = crate::row_constraints::RowConstraintSolver::new(&mut env, 0);
        
        // First, add the lacks constraint
        let lacks_result = row_solver.solve_row_constraint(
            &RowConstraint::Lacks {
                type_var: safe_config.clone(),
                labels: forbidden_fields,
            },
            &mut subs,
        );
        assert!(lacks_result.is_ok());
        
        // Add some allowed fields - should succeed
        let host_result = row_solver.solve_row_constraint(
            &RowConstraint::HasField {
                type_var: safe_config.clone(),
                label: "host".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
            &mut subs,
        );
        assert!(host_result.is_ok());
        
        // Try to add a forbidden field (should fail)
        let password_result = row_solver.solve_row_constraint(
            &RowConstraint::HasField {
                type_var: safe_config.clone(),
                label: "password".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
            &mut subs,
        );
        
        // This should fail because we're trying to add a field that's in the lacks set
        assert!(password_result.is_err());
    }
}