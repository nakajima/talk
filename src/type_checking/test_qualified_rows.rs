//! Tests for the qualified row type system

#[cfg(test)]
mod tests {
    use crate::{
        constraint::Constraint,
        constraint_solver::ConstraintSolver,
        environment::Environment,
        expr_id::ExprID,
        row::{RowConstraint, FieldMetadata},
        ty::Ty,
        type_var_id::TypeVarKind,
        ExprMetaStorage,
    };

    #[test]
    fn test_member_access_with_row_constraint() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a type variable
        let tv = env.new_type_variable(TypeVarKind::Blank, ExprID(0));
        
        // Add a row constraint saying tv has field "x" of type Int
        let row_constraint = Constraint::Row {
            expr_id: ExprID(1),
            constraint: RowConstraint::HasField {
                type_var: tv.clone(),
                label: "x".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        };
        
        // Add a member access constraint
        let result_tv = env.new_type_variable(TypeVarKind::Blank, ExprID(2));
        let member_constraint = Constraint::MemberAccess(
            ExprID(3),
            Ty::TypeVar(tv.clone()),
            "x".to_string(),
            Ty::TypeVar(result_tv.clone()),
        );
        
        // Add constraints to environment
        env.constrain(row_constraint);
        env.constrain(member_constraint);
        
        // Solve constraints
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();
        
        // Check that result_tv is unified with Int
        let resolved = solution.substitutions.apply(&Ty::TypeVar(result_tv), 0, &mut env.context);
        assert_eq!(resolved, Ty::Int);
    }

    #[test]
    fn test_row_concatenation() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create three type variables
        let t1 = env.new_type_variable(TypeVarKind::Blank, ExprID(0));
        let t2 = env.new_type_variable(TypeVarKind::Blank, ExprID(1));
        let t3 = env.new_type_variable(TypeVarKind::Blank, ExprID(2));
        
        // T1 has field x: Int
        let c1 = Constraint::Row {
            expr_id: ExprID(3),
            constraint: RowConstraint::HasField {
                type_var: t1.clone(),
                label: "x".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        };
        
        // T2 has field y: Float
        let c2 = Constraint::Row {
            expr_id: ExprID(4),
            constraint: RowConstraint::HasField {
                type_var: t2.clone(),
                label: "y".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        };
        
        // T1 ⊕ T2 = T3
        let c3 = Constraint::Row {
            expr_id: ExprID(5),
            constraint: RowConstraint::RowConcat {
                left: t1,
                right: t2,
                result: t3.clone(),
            },
        };
        
        // Add constraints
        env.constrain(c1);
        env.constrain(c2);
        env.constrain(c3);
        
        // T3 should now have access to both x and y
        // Test by adding member access constraints
        let rx = env.new_type_variable(TypeVarKind::Blank, ExprID(6));
        let ry = env.new_type_variable(TypeVarKind::Blank, ExprID(7));
        
        env.constrain(Constraint::MemberAccess(
            ExprID(8),
            Ty::TypeVar(t3.clone()),
            "x".to_string(),
            Ty::TypeVar(rx.clone()),
        ));
        
        env.constrain(Constraint::MemberAccess(
            ExprID(9),
            Ty::TypeVar(t3),
            "y".to_string(),
            Ty::TypeVar(ry.clone()),
        ));
        
        // Solve all constraints together
        let mut solver = ConstraintSolver::new(&mut env, &meta, 0);
        let mut solution = solver.solve();
        
        // Check no errors
        assert!(solution.errors.is_empty());
        assert!(solution.unsolved_constraints.is_empty());
        
        let resolved_x = solution.substitutions.apply(&Ty::TypeVar(rx), 0, &mut env.context);
        let resolved_y = solution.substitutions.apply(&Ty::TypeVar(ry), 0, &mut env.context);
        
        assert_eq!(resolved_x, Ty::Int);
        assert_eq!(resolved_y, Ty::Float);
    }
}