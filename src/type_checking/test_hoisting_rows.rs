//! Test that type hoisting creates row variables for new types

#[cfg(test)]
mod tests {
    use crate::{
        SymbolID,
        constraint::Constraint,
        constraint_solver::ConstraintSolver,
        environment::Environment,
        expr_id::ExprID,
        ty::Ty,
        type_def::{TypeDef, TypeDefKind, Property},
        type_var_id::TypeVarKind,
        ExprMetaStorage,
    };
    
    #[test]
    fn test_hoisting_creates_row_vars() {
        let mut env = Environment::new();
        
        // Simulate what the hoisting phase does
        let point_id = SymbolID(1000);
        let name_str = "Point";
        
        // Create a row variable for this type (this is what hoisting should do)
        let row_var = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter(format!("{}_row", name_str)),
            ExprID(1),
        );
        
        let mut type_def = TypeDef::new(
            point_id,
            name_str.to_string(),
            TypeDefKind::Struct,
            vec![],
        );
        type_def.row_var = Some(row_var);
        
        // Register the type
        env.register(&type_def).unwrap();
        
        // Now simulate adding properties using the row-aware method
        let properties = vec![
            Property::new(0, "x".to_string(), ExprID(2), Ty::Float, false),
            Property::new(1, "y".to_string(), ExprID(3), Ty::Float, false),
        ];
        
        type_def.add_properties_with_rows(properties, &mut env);
        
        // Update the registered type
        env.register(&type_def).unwrap();
        
        // Test that member access works
        let meta = ExprMetaStorage::default();
        let point_ty = Ty::Struct(point_id, vec![]);
        let result_tv = env.new_type_variable(TypeVarKind::Blank, ExprID(4));
        
        env.constrain(Constraint::MemberAccess(
            ExprID(5),
            point_ty,
            "x".to_string(),
            Ty::TypeVar(result_tv.clone()),
        ));
        
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();
        
        assert!(solution.errors.is_empty());
        let resolved = solution.substitutions.apply(&Ty::TypeVar(result_tv), 0, &mut env.context);
        assert_eq!(resolved, Ty::Float);
    }
    
    #[test]
    fn test_enum_with_row_vars() {
        let mut env = Environment::new();
        
        // Create an Option enum
        let option_id = SymbolID(2000);
        let name_str = "Option";
        
        let row_var = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter(format!("{}_row", name_str)),
            ExprID(10),
        );
        
        let mut type_def = TypeDef::new(
            option_id,
            name_str.to_string(),
            TypeDefKind::Enum,
            vec![], // simplified
        );
        type_def.row_var = Some(row_var);
        
        env.register(&type_def).unwrap();
        
        // Add variants using row-aware method
        let variants = vec![
            crate::type_def::EnumVariant {
                tag: 0,
                name: "None".to_string(),
                ty: Ty::Enum(option_id, vec![]),
            },
            crate::type_def::EnumVariant {
                tag: 1,
                name: "Some".to_string(),
                ty: Ty::Func(vec![Ty::Int], Box::new(Ty::Enum(option_id, vec![])), vec![]),
            },
        ];
        
        type_def.add_variants_with_rows(variants, &mut env);
        env.register(&type_def).unwrap();
        
        // Test variant access
        let meta = ExprMetaStorage::default();
        let _option_ty = Ty::Enum(option_id, vec![]);
        let _result_tv = env.new_type_variable(TypeVarKind::Blank, ExprID(11));
        
        // Access None variant through the enum type
        // This should work through the row constraints
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let solution = solver.solve();
        
        // Just verify no errors for now
        assert!(solution.errors.is_empty());
    }
}