//! Test the integration of row-based types with the existing TypeDef system

#[cfg(test)]
mod tests {
    use crate::{
        SymbolID,
        constraint::Constraint,
        constraint_solver::ConstraintSolver,
        environment::Environment,
        expr_id::ExprID,
        row::{RowConstraint, FieldMetadata},
        ty::Ty,
        type_def::{TypeDef, TypeDefKind},
        type_var_id::TypeVarKind,
        ExprMetaStorage,
    };
    
    #[test]
    fn test_typedef_with_row_var() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a Point struct with a row variable
        let point_id = SymbolID(1000);
        
        // Create row variable for Point's members
        let point_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Point_row".to_string()),
            ExprID(1),
        );
        
        // Create the TypeDef with row_var set
        let mut point_def = TypeDef::new(
            point_id,
            "Point".to_string(),
            TypeDefKind::Struct,
            vec![],
        );
        point_def.row_var = Some(point_row.clone());
        
        // Register the type
        env.register(&point_def).unwrap();
        
        // Add row constraints for Point's fields
        env.constrain(Constraint::Row {
            expr_id: ExprID(2),
            constraint: RowConstraint::HasField {
                type_var: point_row.clone(),
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
            expr_id: ExprID(3),
            constraint: RowConstraint::HasField {
                type_var: point_row,
                label: "y".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Now test member access
        let point_ty = Ty::Struct(point_id, vec![]);
        let result_tv = env.new_type_variable(TypeVarKind::Blank, ExprID(4));
        
        env.constrain(Constraint::MemberAccess(
            ExprID(5),
            point_ty,
            "x".to_string(),
            Ty::TypeVar(result_tv.clone()),
        ));
        
        // Solve constraints
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();
        
        // Check that member access resolved correctly
        assert!(solution.errors.is_empty());
        let resolved = solution.substitutions.apply(&Ty::TypeVar(result_tv), 0, &mut env.context);
        assert_eq!(resolved, Ty::Float);
    }
    
    #[test]
    fn test_hybrid_typedef() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a Rectangle with both traditional members and row-based members
        let rect_id = SymbolID(2000);
        
        // Create row variable
        let rect_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Rectangle_row".to_string()),
            ExprID(10),
        );
        
        // Create TypeDef with some traditional members
        let mut rect_def = TypeDef::new(
            rect_id,
            "Rectangle".to_string(),
            TypeDefKind::Struct,
            vec![],
        );
        rect_def.row_var = Some(rect_row.clone());
        
        // Add a traditional property (for backwards compatibility)
        rect_def.members.insert(
            "width".to_string(),
            crate::type_def::TypeMember::Property(crate::type_def::Property {
                index: 0,
                name: "width".to_string(),
                expr_id: ExprID(11),
                ty: Ty::Float,
                has_default: false,
            }),
        );
        
        env.register(&rect_def).unwrap();
        
        // Add a row-based property
        env.constrain(Constraint::Row {
            expr_id: ExprID(12),
            constraint: RowConstraint::HasField {
                type_var: rect_row,
                label: "height".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        let rect_ty = Ty::Struct(rect_id, vec![]);
        
        // Test accessing traditional member
        let width_result = env.new_type_variable(TypeVarKind::Blank, ExprID(13));
        env.constrain(Constraint::MemberAccess(
            ExprID(14),
            rect_ty.clone(),
            "width".to_string(),
            Ty::TypeVar(width_result.clone()),
        ));
        
        // Test accessing row-based member
        let height_result = env.new_type_variable(TypeVarKind::Blank, ExprID(15));
        env.constrain(Constraint::MemberAccess(
            ExprID(16),
            rect_ty,
            "height".to_string(),
            Ty::TypeVar(height_result.clone()),
        ));
        
        // Solve
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();
        
        assert!(solution.errors.is_empty());
        
        // Both should resolve to Float
        let resolved_width = solution.substitutions.apply(&Ty::TypeVar(width_result), 0, &mut env.context);
        let resolved_height = solution.substitutions.apply(&Ty::TypeVar(height_result), 0, &mut env.context);
        
        assert_eq!(resolved_width, Ty::Float);
        assert_eq!(resolved_height, Ty::Float);
    }
}