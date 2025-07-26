//! Test row-based enum variant handling

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
    use std::collections::HashMap;
    
    /// Test that enum variants can be defined through row constraints
    #[test]
    fn test_enum_variants_with_rows() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create an enum type with a row variable for variants
        let result_id = SymbolID(8000);
        let result_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("ResultRow".to_string()),
            ExprID(100),
        );
        
        // Add Ok variant
        let t_var = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("T".to_string()),
            ExprID(102),
        );
        env.constrain(Constraint::Row {
            expr_id: ExprID(101),
            constraint: RowConstraint::HasField {
                type_var: result_row.clone(),
                label: "Ok".to_string(),
                field_ty: Ty::TypeVar(t_var),
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        });
        
        // Add Err variant
        let e_var = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("E".to_string()),
            ExprID(104),
        );
        env.constrain(Constraint::Row {
            expr_id: ExprID(103),
            constraint: RowConstraint::HasField {
                type_var: result_row.clone(),
                label: "Err".to_string(),
                field_ty: Ty::TypeVar(e_var),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        });
        
        let result_def = TypeDef {
            symbol_id: result_id,
            name_str: "Result".to_string(),
            kind: TypeDefKind::Enum,
            type_parameters: vec![],
            members: HashMap::new(),
            conformances: vec![],
            row_var: Some(result_row.clone()),
        };
        
        env.register(&result_def).unwrap();
        
        // Solve constraints
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Access enum variants through member access
        let ok_type = env.new_type_variable(TypeVarKind::Blank, ExprID(110));
        env.constrain(Constraint::MemberAccess(
            ExprID(111),
            Ty::TypeVar(result_row.clone()),
            "Ok".to_string(),
            Ty::TypeVar(ok_type.clone()),
        ));
        
        let err_type = env.new_type_variable(TypeVarKind::Blank, ExprID(112));
        env.constrain(Constraint::MemberAccess(
            ExprID(113),
            Ty::TypeVar(result_row.clone()),
            "Err".to_string(),
            Ty::TypeVar(err_type.clone()),
        ));
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test composing enum variants from multiple sources
    #[test]
    fn test_composed_enum_variants() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create basic error variants
        let basic_errors = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("BasicErrors".to_string()),
            ExprID(200),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(201),
            constraint: RowConstraint::HasField {
                type_var: basic_errors.clone(),
                label: "NotFound".to_string(),
                field_ty: Ty::Void,
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(202),
            constraint: RowConstraint::HasField {
                type_var: basic_errors.clone(),
                label: "InvalidInput".to_string(),
                field_ty: Ty::string(),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        });
        
        // Create network error variants
        let network_errors = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("NetworkErrors".to_string()),
            ExprID(210),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(211),
            constraint: RowConstraint::HasField {
                type_var: network_errors.clone(),
                label: "Timeout".to_string(),
                field_ty: Ty::Int, // timeout in seconds
                metadata: FieldMetadata::EnumCase { tag: 2 },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(212),
            constraint: RowConstraint::HasField {
                type_var: network_errors.clone(),
                label: "ConnectionRefused".to_string(),
                field_ty: Ty::Void,
                metadata: FieldMetadata::EnumCase { tag: 3 },
            },
        });
        
        // Compose all errors
        let all_errors = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("AllErrors".to_string()),
            ExprID(220),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(221),
            constraint: RowConstraint::RowConcat {
                left: basic_errors.clone(),
                right: network_errors.clone(),
                result: all_errors.clone(),
            },
        });
        
        // Create the enum
        let error_enum_id = SymbolID(8001);
        let error_enum_def = TypeDef {
            symbol_id: error_enum_id,
            name_str: "Error".to_string(),
            kind: TypeDefKind::Enum,
            type_parameters: vec![],
            members: HashMap::new(),
            conformances: vec![],
            row_var: Some(all_errors.clone()),
        };
        
        env.register(&error_enum_def).unwrap();
        
        // Solve constraints
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Verify we can access all variants
        for variant in ["NotFound", "InvalidInput", "Timeout", "ConnectionRefused"] {
            let variant_type = env.new_type_variable(TypeVarKind::Blank, ExprID(230));
            env.constrain(Constraint::MemberAccess(
                ExprID(231),
                Ty::TypeVar(all_errors.clone()),
                variant.to_string(),
                Ty::TypeVar(variant_type),
            ));
        }
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test enum variant restrictions
    #[test]
    fn test_restricted_enum_variants() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create full error enum
        let full_errors = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("FullErrors".to_string()),
            ExprID(300),
        );
        
        for (i, (variant, ty)) in [
            ("UserError", Ty::string()),
            ("SystemError", Ty::string()),
            ("NetworkError", Ty::string()),
            ("InternalError", Ty::string()),
        ].iter().enumerate() {
            env.constrain(Constraint::Row {
                expr_id: ExprID(301 + i as i32),
                constraint: RowConstraint::HasField {
                    type_var: full_errors.clone(),
                    label: variant.to_string(),
                    field_ty: ty.clone(),
                    metadata: FieldMetadata::EnumCase { tag: i },
                },
            });
        }
        
        // Create public-facing error enum without internal errors
        let public_errors = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("PublicErrors".to_string()),
            ExprID(310),
        );
        
        let mut restricted = crate::row::LabelSet::new();
        restricted.insert("InternalError".to_string());
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(311),
            constraint: RowConstraint::RowRestrict {
                source: full_errors.clone(),
                labels: restricted,
                result: public_errors.clone(),
            },
        });
        
        // Solve all constraints together
        let user_error = env.new_type_variable(TypeVarKind::Blank, ExprID(320));
        env.constrain(Constraint::MemberAccess(
            ExprID(321),
            Ty::TypeVar(public_errors.clone()),
            "UserError".to_string(),
            Ty::TypeVar(user_error),
        ));
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Verify internal error is not accessible
        let internal_error = env.new_type_variable(TypeVarKind::Blank, ExprID(330));
        env.constrain(Constraint::MemberAccess(
            ExprID(331),
            Ty::TypeVar(public_errors),
            "InternalError".to_string(),
            Ty::TypeVar(internal_error),
        ));
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(!solution.errors.is_empty());
    }
}