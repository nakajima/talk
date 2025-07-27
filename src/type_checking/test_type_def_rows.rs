//! Tests for row-based type definitions

#[cfg(test)]
mod tests {
    use crate::{
        ExprMetaStorage, SymbolID,
        constraint::Constraint,
        constraint_solver::ConstraintSolver,
        environment::Environment,
        expr_id::ExprID,
        row::{FieldMetadata, RowConstraint},
        ty::Ty,
        type_def_rows::{RowTypeDefBuilder, TypeDefKind},
        type_var_id::TypeVarKind,
    };

    #[test]
    fn test_struct_with_row_constraints() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();

        // Create a Point struct with x, y fields using row constraints
        let point_id = SymbolID(1000);
        let point_def = RowTypeDefBuilder::new(
            point_id,
            "Point".to_string(),
            TypeDefKind::Struct,
            vec![], // no type parameters
            &mut env,
        )
        .with_property("x".to_string(), Ty::Float, 0, false, false, ExprID(1))
        .with_property("y".to_string(), Ty::Float, 1, false, false, ExprID(2))
        .build();

        // Simulate accessing point.x
        let _point_ty = Ty::Struct(point_id, vec![]);
        let result_tv = env.new_type_variable(TypeVarKind::Blank, ExprID(3));

        // For member access on a struct, we need to:
        // 1. Look up the struct's row variable
        // 2. Add a constraint that links the struct type to its row variable

        // Add constraint linking struct type to its row variable
        env.constrain(Constraint::Row {
            expr_id: ExprID(4),
            constraint: RowConstraint::HasRow {
                type_var: point_def.row_var.clone(),
                row: crate::row::RowSpec::empty(), // Will be populated by solver
                extension: None,
            },
        });

        // Now we can access members through the row variable
        env.constrain(Constraint::MemberAccess(
            ExprID(5),
            Ty::TypeVar(point_def.row_var.clone()),
            "x".to_string(),
            Ty::TypeVar(result_tv.clone()),
        ));

        // Solve constraints
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();

        // Check that result_tv is unified with Float
        assert!(solution.errors.is_empty());
        let resolved = solution
            .substitutions
            .apply(&Ty::TypeVar(result_tv), 0, &mut env.context);
        assert_eq!(resolved, Ty::Float);
    }

    #[test]
    fn test_protocol_with_method_requirements() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();

        // Create a Drawable protocol with a draw method requirement
        let drawable_id = SymbolID(2000);
        let drawable_def = RowTypeDefBuilder::new(
            drawable_id,
            "Drawable".to_string(),
            TypeDefKind::Protocol,
            vec![], // no type parameters for simplicity
            &mut env,
        )
        .build();

        // Add draw method requirement
        drawable_def.add_method_requirement(
            &mut env,
            "draw".to_string(),
            Ty::Func(vec![], Box::new(Ty::Void), vec![]),
            ExprID(10),
        );

        // Create a type variable constrained to conform to Drawable
        let t = env.new_type_variable(TypeVarKind::Blank, ExprID(11));

        // Add conformance constraint (this would link t's row to drawable's row)
        env.constrain(Constraint::Row {
            expr_id: ExprID(12),
            constraint: RowConstraint::HasField {
                type_var: t.clone(),
                label: "draw".to_string(),
                field_ty: Ty::Func(vec![], Box::new(Ty::Void), vec![]),
                metadata: FieldMetadata::MethodRequirement,
            },
        });

        // Access the draw method
        let result_tv = env.new_type_variable(TypeVarKind::Blank, ExprID(13));
        env.constrain(Constraint::MemberAccess(
            ExprID(14),
            Ty::TypeVar(t),
            "draw".to_string(),
            Ty::TypeVar(result_tv.clone()),
        ));

        // Solve
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();

        assert!(solution.errors.is_empty());
        let resolved = solution
            .substitutions
            .apply(&Ty::TypeVar(result_tv), 0, &mut env.context);
        assert_eq!(resolved, Ty::Func(vec![], Box::new(Ty::Void), vec![]));
    }

    #[test]
    fn test_enum_with_variants() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();

        // Create an Option enum with Some and None variants
        let option_id = SymbolID(3000);
        let t_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("T".to_string()),
            ExprID(20),
        );

        let option_def = RowTypeDefBuilder::new(
            option_id,
            "Option".to_string(),
            TypeDefKind::Enum,
            vec![], // simplified - would have type parameter
            &mut env,
        )
        .build();

        // Add variants
        option_def.add_variant(
            &mut env,
            "None".to_string(),
            Ty::Enum(option_id, vec![Ty::TypeVar(t_param.clone())]),
            0,
            ExprID(21),
        );

        option_def.add_variant(
            &mut env,
            "Some".to_string(),
            Ty::Func(
                vec![Ty::TypeVar(t_param.clone())],
                Box::new(Ty::Enum(option_id, vec![Ty::TypeVar(t_param)])),
                vec![],
            ),
            1,
            ExprID(22),
        );

        // Test accessing None variant
        let result_tv = env.new_type_variable(TypeVarKind::Blank, ExprID(23));
        env.constrain(Constraint::MemberAccess(
            ExprID(24),
            Ty::TypeVar(option_def.row_var.clone()),
            "None".to_string(),
            Ty::TypeVar(result_tv.clone()),
        ));

        // Solve
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();

        assert!(solution.errors.is_empty());
        // Result should be the enum type itself for None variant
        let resolved = solution
            .substitutions
            .apply(&Ty::TypeVar(result_tv), 0, &mut env.context);
        match resolved {
            Ty::Enum(id, _) => assert_eq!(id, option_id),
            _ => panic!("Expected enum type"),
        }
    }
}
