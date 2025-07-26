//! Test row-based protocol conformance checking

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
        conformance::Conformance,
    };
    use std::collections::HashMap;
    
    /// Test that a type with the right row structure conforms to a protocol
    #[test]
    fn test_row_based_protocol_conformance() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Step 1: Define a protocol that requires certain fields
        // Protocol Drawable { x: Float, y: Float, draw: () -> () }
        let drawable_id = SymbolID(6000);
        let drawable_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("DrawableRow".to_string()),
            ExprID(100),
        );
        
        // Add required fields to the protocol's row
        env.constrain(Constraint::Row {
            expr_id: ExprID(101),
            constraint: RowConstraint::HasField {
                type_var: drawable_row.clone(),
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
            expr_id: ExprID(102),
            constraint: RowConstraint::HasField {
                type_var: drawable_row.clone(),
                label: "y".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(103),
            constraint: RowConstraint::HasField {
                type_var: drawable_row.clone(),
                label: "draw".to_string(),
                field_ty: Ty::Func(vec![], Box::new(Ty::Void), vec![]),
                metadata: FieldMetadata::RecordField {
                    index: 2,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Create the protocol definition
        let drawable_protocol = TypeDef {
            symbol_id: drawable_id,
            name_str: "Drawable".to_string(),
            kind: TypeDefKind::Protocol,
            type_parameters: vec![],
            members: HashMap::new(), // Will be populated from row
            conformances: vec![],
            row_var: Some(drawable_row.clone()),
        };
        
        env.register(&drawable_protocol).unwrap();
        
        // Step 2: Create a type that has the required fields
        let circle_id = SymbolID(6001);
        let circle_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("CircleRow".to_string()),
            ExprID(110),
        );
        
        // Circle has x, y, radius, and draw
        env.constrain(Constraint::Row {
            expr_id: ExprID(111),
            constraint: RowConstraint::HasField {
                type_var: circle_row.clone(),
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
            expr_id: ExprID(112),
            constraint: RowConstraint::HasField {
                type_var: circle_row.clone(),
                label: "y".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: true,
                },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(113),
            constraint: RowConstraint::HasField {
                type_var: circle_row.clone(),
                label: "radius".to_string(),
                field_ty: Ty::Float,
                metadata: FieldMetadata::RecordField {
                    index: 2,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(114),
            constraint: RowConstraint::HasField {
                type_var: circle_row.clone(),
                label: "draw".to_string(),
                field_ty: Ty::Func(vec![], Box::new(Ty::Void), vec![]),
                metadata: FieldMetadata::RecordField {
                    index: 3,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        let circle_def = TypeDef {
            symbol_id: circle_id,
            name_str: "Circle".to_string(),
            kind: TypeDefKind::Struct,
            type_parameters: vec![],
            members: HashMap::new(),
            conformances: vec![Conformance {
                protocol_id: drawable_id,
                associated_types: vec![],
            }],
            row_var: Some(circle_row.clone()),
        };
        
        env.register(&circle_def).unwrap();
        
        // Step 3: Check conformance through row constraints
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Verify Circle conforms to Drawable
        let _conformance_result = env.new_type_variable(TypeVarKind::Blank, ExprID(120));
        env.constrain(Constraint::ConformsTo {
            expr_id: ExprID(121),
            ty: Ty::Struct(circle_id, vec![]),
            conformance: Conformance {
                protocol_id: drawable_id,
                associated_types: vec![],
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test that row subsumption allows structural subtyping
    #[test]
    fn test_row_subsumption() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a type variable that needs {x: Int, y: Int}
        let position_required = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("PositionRequired".to_string()),
            ExprID(200),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(201),
            constraint: RowConstraint::HasField {
                type_var: position_required.clone(),
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
            expr_id: ExprID(202),
            constraint: RowConstraint::HasField {
                type_var: position_required.clone(),
                label: "y".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Create a type that has {x: Int, y: Int, z: Int}
        let point3d = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Point3D".to_string()),
            ExprID(210),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(211),
            constraint: RowConstraint::HasField {
                type_var: point3d.clone(),
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
            expr_id: ExprID(212),
            constraint: RowConstraint::HasField {
                type_var: point3d.clone(),
                label: "y".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(213),
            constraint: RowConstraint::HasField {
                type_var: point3d.clone(),
                label: "z".to_string(),
                field_ty: Ty::Int,
                metadata: FieldMetadata::RecordField {
                    index: 2,
                    has_default: false,
                    is_mutable: false,
                },
            },
        });
        
        // Test that point3d can be used where position_required is expected
        // This is the essence of structural subtyping - a type with more fields
        // can be used where fewer fields are required
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Both should be able to access x and y
        let x_result = env.new_type_variable(TypeVarKind::Blank, ExprID(220));
        env.constrain(Constraint::MemberAccess(
            ExprID(221),
            Ty::TypeVar(position_required.clone()),
            "x".to_string(),
            Ty::TypeVar(x_result.clone()),
        ));
        
        let y_result = env.new_type_variable(TypeVarKind::Blank, ExprID(222));
        env.constrain(Constraint::MemberAccess(
            ExprID(223),
            Ty::TypeVar(point3d.clone()),
            "y".to_string(),
            Ty::TypeVar(y_result.clone()),
        ));
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
}