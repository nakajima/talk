//! Comprehensive test of the row-based type system integration

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    
    use crate::{
        SymbolID,
        conformance::Conformance,
        constraint::Constraint,
        constraint_solver::ConstraintSolver,
        environment::Environment,
        expr_id::ExprID,
        row::{RowConstraint, FieldMetadata},
        ty::Ty,
        type_def::{TypeDef, TypeDefKind, Property, Method},
        type_var_id::TypeVarKind,
        ExprMetaStorage,
    };
    
    /// This test demonstrates the complete row-based type system:
    /// 1. Protocol with row-based requirements
    /// 2. Struct conforming to protocol through row constraints
    /// 3. Generic function using protocol constraints
    /// 4. Row concatenation for extending types
    #[test]
    fn test_complete_row_system() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Step 1: Define a Drawable protocol with row constraints
        let drawable_id = SymbolID(1000);
        let drawable_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Drawable_row".to_string()),
            ExprID(1),
        );
        
        let drawable_def = TypeDef {
            symbol_id: drawable_id,
            name_str: "Drawable".to_string(),
            kind: TypeDefKind::Protocol,
            type_parameters: vec![],
            members: HashMap::new(),
            conformances: vec![],
            row_var: Some(drawable_row.clone()),
        };
        
        env.register(&drawable_def).unwrap();
        
        // Add draw method requirement via row constraint
        env.constrain(Constraint::Row {
            expr_id: ExprID(2),
            constraint: RowConstraint::HasField {
                type_var: drawable_row,
                label: "draw".to_string(),
                field_ty: Ty::Func(vec![], Box::new(Ty::Void), vec![]),
                metadata: FieldMetadata::MethodRequirement,
            },
        });
        
        // Step 2: Define a Circle struct that conforms to Drawable
        let circle_id = SymbolID(2000);
        let circle_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Circle_row".to_string()),
            ExprID(3),
        );
        
        let mut circle_def = TypeDef {
            symbol_id: circle_id,
            name_str: "Circle".to_string(),
            kind: TypeDefKind::Struct,
            type_parameters: vec![],
            members: HashMap::new(),
            conformances: vec![
                Conformance {
                    protocol_id: drawable_id,
                    associated_types: vec![],
                }
            ],
            row_var: Some(circle_row.clone()),
        };
        
        env.register(&circle_def).unwrap();
        
        // Add properties and methods via row constraints
        let properties = vec![
            Property::new(0, "x".to_string(), ExprID(4), Ty::Float, false),
            Property::new(1, "y".to_string(), ExprID(5), Ty::Float, false),
            Property::new(2, "radius".to_string(), ExprID(6), Ty::Float, false),
        ];
        
        circle_def.add_properties_with_rows(properties, &mut env);
        
        let methods = vec![
            Method::new(
                "draw".to_string(),
                ExprID(7),
                Ty::Func(vec![], Box::new(Ty::Void), vec![]),
            ),
        ];
        
        circle_def.add_methods_with_rows(methods, &mut env);
        
        env.register(&circle_def).unwrap();
        
        // Step 3: Test member access on Circle
        let circle_ty = Ty::Struct(circle_id, vec![]);
        let radius_result = env.new_type_variable(TypeVarKind::Blank, ExprID(8));
        
        env.constrain(Constraint::MemberAccess(
            ExprID(9),
            circle_ty.clone(),
            "radius".to_string(),
            Ty::TypeVar(radius_result.clone()),
        ));
        
        let draw_result = env.new_type_variable(TypeVarKind::Blank, ExprID(10));
        
        env.constrain(Constraint::MemberAccess(
            ExprID(11),
            circle_ty,
            "draw".to_string(),
            Ty::TypeVar(draw_result.clone()),
        ));
        
        // Solve constraints
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();
        
        assert!(solution.errors.is_empty());
        
        // Check results
        let resolved_radius = solution.substitutions.apply(&Ty::TypeVar(radius_result), 0, &mut env.context);
        assert_eq!(resolved_radius, Ty::Float);
        
        let resolved_draw = solution.substitutions.apply(&Ty::TypeVar(draw_result), 0, &mut env.context);
        assert_eq!(resolved_draw, Ty::Func(vec![], Box::new(Ty::Void), vec![]));
    }
    
    /// Test row concatenation for type composition
    #[test]
    fn test_row_composition() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a Position row with x, y
        let position_row = env.new_type_variable(TypeVarKind::Blank, ExprID(20));
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(21),
            constraint: RowConstraint::HasField {
                type_var: position_row.clone(),
                label: "x".to_string(),
                field_ty: Ty::Float,
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
                type_var: position_row.clone(),
                label: "y".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Create a Size row with width, height
        let size_row = env.new_type_variable(TypeVarKind::Blank, ExprID(23));
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(24),
            constraint: RowConstraint::HasField {
                type_var: size_row.clone(),
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
            expr_id: ExprID(25),
            constraint: RowConstraint::HasField {
                type_var: size_row.clone(),
                label: "height".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Create a Rectangle by concatenating Position and Size
        let rect_row = env.new_type_variable(TypeVarKind::Blank, ExprID(26));
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(27),
            constraint: RowConstraint::RowConcat {
                left: position_row,
                right: size_row,
                result: rect_row.clone(),
            },
        });
        
        // Test that rect_row has all fields
        let x_result = env.new_type_variable(TypeVarKind::Blank, ExprID(28));
        env.constrain(Constraint::MemberAccess(
            ExprID(29),
            Ty::TypeVar(rect_row.clone()),
            "x".to_string(),
            Ty::TypeVar(x_result.clone()),
        ));
        
        let width_result = env.new_type_variable(TypeVarKind::Blank, ExprID(30));
        env.constrain(Constraint::MemberAccess(
            ExprID(31),
            Ty::TypeVar(rect_row),
            "width".to_string(),
            Ty::TypeVar(width_result.clone()),
        ));
        
        // Solve
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();
        
        assert!(solution.errors.is_empty());
        
        // Both should resolve to Float
        let resolved_x = solution.substitutions.apply(&Ty::TypeVar(x_result), 0, &mut env.context);
        let resolved_width = solution.substitutions.apply(&Ty::TypeVar(width_result), 0, &mut env.context);
        
        assert_eq!(resolved_x, Ty::Float);
        assert_eq!(resolved_width, Ty::Float);
    }
}