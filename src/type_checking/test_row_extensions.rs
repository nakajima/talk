//! Tests for row extension mechanism
//! 
//! Row extensions allow types to be extended with additional fields,
//! enabling row polymorphism and flexible type composition.

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    
    use crate::{
        environment::Environment,
        expr_id::ExprID,
        row::{FieldInfo, FieldMetadata, RowConstraint, RowSpec},
        row_constraints::RowConstraintSolver,
        substitutions::Substitutions,
        ty::Ty,
        type_var_id::{TypeVarID, TypeVarKind},
    };

    /// Test basic row extension
    #[test]
    fn test_row_extension_basic() {
        let mut env = Environment::new();
        let mut solver = RowConstraintSolver::new(&mut env, 0);
        let mut type_subs = Substitutions::new();
        
        // Create a base type with name field
        let base = TypeVarID::new(1, TypeVarKind::Blank, ExprID(1));
        let mut base_fields = BTreeMap::new();
        base_fields.insert(
            "name".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(1),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        // Create an extension with age field  
        let extension = TypeVarID::new(2, TypeVarKind::Blank, ExprID(2));
        let extension_constraint = RowConstraint::HasField {
            type_var: extension.clone(),
            label: "age".to_string(),
            field_ty: Ty::Int,
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };
        solver.solve_row_constraint(&extension_constraint, &mut type_subs).unwrap();
        
        // Create a type that has base fields and is extended by extension
        let extended = TypeVarID::new(3, TypeVarKind::Blank, ExprID(3));
        let constraint = RowConstraint::HasRow {
            type_var: extended.clone(),
            row: RowSpec { fields: base_fields },
            extension: Some(extension.clone()),
        };
        
        solver.solve_row_constraint(&constraint, &mut type_subs).unwrap();
        
        // Check that extended has both name and age fields
        assert!(solver.has_field(&extended, &"name".to_string()).is_some());
        assert!(solver.has_field(&extended, &"age".to_string()).is_some());
        
        // Check that all fields includes both
        let all_fields = solver.get_all_fields(&extended);
        assert_eq!(all_fields.len(), 2);
        assert!(all_fields.contains_key(&"name".to_string()));
        assert!(all_fields.contains_key(&"age".to_string()));
    }
    
    /// Test that extended types are not exact
    #[test]
    fn test_extended_types_not_exact() {
        let mut env = Environment::new();
        let mut solver = RowConstraintSolver::new(&mut env, 0);
        let mut type_subs = Substitutions::new();
        
        // Create a type with an exact row
        let exact = TypeVarID::new(1, TypeVarKind::Blank, ExprID(1));
        let mut exact_fields = BTreeMap::new();
        exact_fields.insert(
            "x".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(1),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        let exact_constraint = RowConstraint::HasExactRow {
            type_var: exact.clone(),
            row: RowSpec { fields: exact_fields.clone() },
        };
        
        solver.set_all_constraints(&[exact_constraint.clone()]);
        solver.solve_row_constraint(&exact_constraint, &mut type_subs).unwrap();
        
        // Try to add a field - should fail
        let add_field = RowConstraint::HasField {
            type_var: exact.clone(),
            label: "y".to_string(),
            field_ty: Ty::Int,
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };
        
        assert!(solver.solve_row_constraint(&add_field, &mut type_subs).is_err());
        
        // Now create an extended type with the same base fields
        let extension = TypeVarID::new(2, TypeVarKind::Blank, ExprID(2));
        let extended = TypeVarID::new(3, TypeVarKind::Blank, ExprID(3));
        
        let extended_constraint = RowConstraint::HasRow {
            type_var: extended.clone(),
            row: RowSpec { fields: exact_fields },
            extension: Some(extension.clone()),
        };
        
        solver.solve_row_constraint(&extended_constraint, &mut type_subs).unwrap();
        
        // Adding a field to the extended type should succeed because it's not exact
        let add_to_extended = RowConstraint::HasField {
            type_var: extended.clone(),
            label: "y".to_string(),
            field_ty: Ty::Int,
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };
        
        assert!(solver.solve_row_constraint(&add_to_extended, &mut type_subs).is_ok());
    }
    
    /// Test row polymorphism with extensions
    #[test]
    fn test_row_polymorphism_with_extensions() {
        let mut env = Environment::new();
        let mut solver = RowConstraintSolver::new(&mut env, 0);
        let mut type_subs = Substitutions::new();
        
        // Create a polymorphic function that works on any type with a name field
        let param_type = TypeVarID::new(1, TypeVarKind::Blank, ExprID(1));
        let row_var = TypeVarID::new(2, TypeVarKind::Blank, ExprID(2));
        
        let mut required_fields = BTreeMap::new();
        required_fields.insert(
            "name".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(1),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        let param_constraint = RowConstraint::HasRow {
            type_var: param_type.clone(),
            row: RowSpec { fields: required_fields },
            extension: Some(row_var.clone()),
        };
        
        solver.solve_row_constraint(&param_constraint, &mut type_subs).unwrap();
        
        // Create a concrete type with name and age
        let person = TypeVarID::new(3, TypeVarKind::Blank, ExprID(3));
        let name_constraint = RowConstraint::HasField {
            type_var: person.clone(),
            label: "name".to_string(),
            field_ty: Ty::string(),
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };
        let age_constraint = RowConstraint::HasField {
            type_var: person.clone(),
            label: "age".to_string(),
            field_ty: Ty::Int,
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };
        
        solver.solve_row_constraint(&name_constraint, &mut type_subs).unwrap();
        solver.solve_row_constraint(&age_constraint, &mut type_subs).unwrap();
        
        // The person type should be usable where param_type is expected
        // because it has the required name field plus additional fields
        assert!(solver.has_field(&person, &"name".to_string()).is_some());
        assert!(solver.has_field(&person, &"age".to_string()).is_some());
    }
    
    /// Test chained extensions
    #[test]
    fn test_chained_extensions() {
        let mut env = Environment::new();
        let mut solver = RowConstraintSolver::new(&mut env, 0);
        let mut type_subs = Substitutions::new();
        
        // Create a chain of extensions: base -> ext1 -> ext2
        let base = TypeVarID::new(1, TypeVarKind::Blank, ExprID(1));
        let ext1 = TypeVarID::new(2, TypeVarKind::Blank, ExprID(2));
        let ext2 = TypeVarID::new(3, TypeVarKind::Blank, ExprID(3));
        
        // Base has field 'a'
        let base_constraint = RowConstraint::HasField {
            type_var: base.clone(),
            label: "a".to_string(),
            field_ty: Ty::Int,
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };
        solver.solve_row_constraint(&base_constraint, &mut type_subs).unwrap();
        
        // ext1 extends base and adds field 'b'
        let ext1_base = RowConstraint::HasRow {
            type_var: ext1.clone(),
            row: RowSpec { fields: BTreeMap::new() },
            extension: Some(base.clone()),
        };
        let ext1_field = RowConstraint::HasField {
            type_var: ext1.clone(),
            label: "b".to_string(),
            field_ty: Ty::string(),
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };
        solver.solve_row_constraint(&ext1_base, &mut type_subs).unwrap();
        solver.solve_row_constraint(&ext1_field, &mut type_subs).unwrap();
        
        // ext2 extends ext1 and adds field 'c'
        let ext2_base = RowConstraint::HasRow {
            type_var: ext2.clone(),
            row: RowSpec { fields: BTreeMap::new() },
            extension: Some(ext1.clone()),
        };
        let ext2_field = RowConstraint::HasField {
            type_var: ext2.clone(),
            label: "c".to_string(),
            field_ty: Ty::Bool,
            metadata: FieldMetadata::RecordField {
                index: 0,
                has_default: false,
                is_mutable: false,
            },
        };
        solver.solve_row_constraint(&ext2_base, &mut type_subs).unwrap();
        solver.solve_row_constraint(&ext2_field, &mut type_subs).unwrap();
        
        // ext2 should have all three fields
        assert!(solver.has_field(&ext2, &"a".to_string()).is_some());
        assert!(solver.has_field(&ext2, &"b".to_string()).is_some());
        assert!(solver.has_field(&ext2, &"c".to_string()).is_some());
        
        let all_fields = solver.get_all_fields(&ext2);
        assert_eq!(all_fields.len(), 3);
    }
}