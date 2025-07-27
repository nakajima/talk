//! Example showing how to use the row-based type system

#[cfg(test)]
mod examples {
    use crate::{
        ExprMetaStorage, SymbolID,
        constraint::Constraint,
        constraint_solver::ConstraintSolver,
        environment::Environment,
        expr_id::ExprID,
        ty::Ty,
        type_def::{Method, Property, TypeDef, TypeDefKind},
        type_var_id::TypeVarKind,
    };

    /// Example: Creating a struct with row-based members
    #[test]
    fn example_struct_with_rows() {
        let mut env = Environment::new();

        // Step 1: Create the TypeDef
        let point_id = SymbolID(1000);
        let mut point_def =
            TypeDef::new(point_id, "Point".to_string(), TypeDefKind::Struct, vec![]);

        // Step 2: Register the type
        env.register(&point_def).unwrap();

        // Step 3: Add properties using row-aware method
        // This automatically creates a row variable and adds constraints
        let properties = vec![
            Property::new(0, "x".to_string(), ExprID(1), Ty::Float, false),
            Property::new(1, "y".to_string(), ExprID(2), Ty::Float, false),
        ];

        point_def.add_properties_with_rows(properties, &mut env);

        // Step 4: Re-register to update the type
        env.register(&point_def).unwrap();

        // Step 5: Use the type - member access works through row constraints
        let meta = ExprMetaStorage::default();
        let point_ty = Ty::Struct(point_id, vec![]);
        let x_result = env.new_type_variable(TypeVarKind::Blank, ExprID(3));

        env.constrain(Constraint::MemberAccess(
            ExprID(4),
            point_ty,
            "x".to_string(),
            Ty::TypeVar(x_result.clone()),
        ));

        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();

        assert!(solution.errors.is_empty());
        let resolved = solution
            .substitutions
            .apply(&Ty::TypeVar(x_result), 0, &mut env.context);
        assert_eq!(resolved, Ty::Float);
    }

    /// Example: Building a type with multiple sets of members using rows
    #[test]
    fn example_building_type_with_rows() {
        let mut env = Environment::new();

        // Create a type and add members in multiple calls
        let rect_id = SymbolID(2000);
        let mut rect_def = TypeDef::new(
            rect_id,
            "Rectangle".to_string(),
            TypeDefKind::Struct,
            vec![],
        );

        env.register(&rect_def).unwrap();

        // Add some properties using the row-based approach
        rect_def.add_properties_with_rows(
            vec![
                Property::new(0, "width".to_string(), ExprID(10), Ty::Float, false),
                Property::new(1, "height".to_string(), ExprID(11), Ty::Float, false),
            ],
            &mut env,
        );

        // Add more properties using rows
        rect_def.add_properties_with_rows(
            vec![
                Property::new(2, "x".to_string(), ExprID(12), Ty::Float, false),
                Property::new(3, "y".to_string(), ExprID(13), Ty::Float, false),
            ],
            &mut env,
        );

        // Add a method using rows
        rect_def.add_methods_with_rows(
            vec![Method::new(
                "area".to_string(),
                ExprID(14),
                Ty::Func(vec![], Box::new(Ty::Float), vec![]),
            )],
            &mut env,
        );

        env.register(&rect_def).unwrap();

        // All members are accessible through row constraints
        let meta = ExprMetaStorage::default();
        let rect_ty = Ty::Struct(rect_id, vec![]);

        // Test first set of members
        let width_result = env.new_type_variable(TypeVarKind::Blank, ExprID(15));
        env.constrain(Constraint::MemberAccess(
            ExprID(16),
            rect_ty.clone(),
            "width".to_string(),
            Ty::TypeVar(width_result.clone()),
        ));

        // Test second set of members
        let x_result = env.new_type_variable(TypeVarKind::Blank, ExprID(17));
        env.constrain(Constraint::MemberAccess(
            ExprID(18),
            rect_ty.clone(),
            "x".to_string(),
            Ty::TypeVar(x_result.clone()),
        ));

        // Test method added with rows
        let area_result = env.new_type_variable(TypeVarKind::Blank, ExprID(19));
        env.constrain(Constraint::MemberAccess(
            ExprID(20),
            rect_ty,
            "area".to_string(),
            Ty::TypeVar(area_result.clone()),
        ));

        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();

        assert!(solution.errors.is_empty());

        // All members resolve correctly
        let resolved_width =
            solution
                .substitutions
                .apply(&Ty::TypeVar(width_result), 0, &mut env.context);
        let resolved_x = solution
            .substitutions
            .apply(&Ty::TypeVar(x_result), 0, &mut env.context);
        let resolved_area =
            solution
                .substitutions
                .apply(&Ty::TypeVar(area_result), 0, &mut env.context);

        assert_eq!(resolved_width, Ty::Float);
        assert_eq!(resolved_x, Ty::Float);
        assert_eq!(resolved_area, Ty::Func(vec![], Box::new(Ty::Float), vec![]));
    }
}
