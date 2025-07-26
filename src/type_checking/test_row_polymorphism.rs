//! Test row polymorphism for generic functions

#[cfg(test)]
mod tests {
    use crate::{
        constraint::Constraint,
        environment::Environment,
        expr_id::ExprID,
        row::{RowConstraint, FieldMetadata, RowSpec, FieldInfo},
        ty::Ty,
        type_var_id::TypeVarKind,
        ExprMetaStorage,
    };
    use std::collections::{BTreeMap, BTreeSet};
    
    /// Test basic row polymorphism - function generic over row structure
    #[test]
    fn test_basic_row_polymorphism() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Function that's polymorphic over a row variable
        // func getX<R: {x: Int, ..R}>(obj: {x: Int, ..R}) -> Int {
        //     obj.x
        // }
        
        // Create the row type parameter R
        let row_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("R".to_string()),
            ExprID(1),
        );
        
        // Create the parameter type that has x: Int and extends with R
        let param_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(2),
        );
        
        let mut base_fields = BTreeMap::new();
        base_fields.insert(
            "x".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(3),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(4),
            constraint: RowConstraint::HasRow {
                type_var: param_type.clone(),
                row: RowSpec { fields: base_fields },
                extension: Some(row_param.clone()),
            },
        });
        
        // Test calling with different concrete types
        
        // Type with just x
        let point2d = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(10),
        );
        
        let mut point2d_fields = BTreeMap::new();
        point2d_fields.insert(
            "x".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(11),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(12),
            constraint: RowConstraint::HasExactRow {
                type_var: point2d.clone(),
                row: RowSpec { fields: point2d_fields },
            },
        });
        
        // Type with x and y
        let point3d = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(20),
        );
        
        let mut point3d_fields = BTreeMap::new();
        point3d_fields.insert(
            "x".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(21),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        point3d_fields.insert(
            "y".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(22),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        point3d_fields.insert(
            "z".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(23),
                metadata: FieldMetadata::RecordField {
                    index: 2,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(24),
            constraint: RowConstraint::HasExactRow {
                type_var: point3d.clone(),
                row: RowSpec { fields: point3d_fields },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test row polymorphism with multiple constraints
    #[test]
    fn test_row_polymorphism_multiple_constraints() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Function with multiple row constraints
        // func combine<R: {x: Int, ..R} & {y: Int, ..R}>(
        //     obj: {x: Int, y: Int, ..R}
        // ) -> Int {
        //     obj.x + obj.y
        // }
        
        let row_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("R".to_string()),
            ExprID(30),
        );
        
        let param_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(31),
        );
        
        let mut required_fields = BTreeMap::new();
        required_fields.insert(
            "x".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(32),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        required_fields.insert(
            "y".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(33),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(34),
            constraint: RowConstraint::HasRow {
                type_var: param_type.clone(),
                row: RowSpec { fields: required_fields },
                extension: Some(row_param.clone()),
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test row polymorphism with lacks constraints
    #[test]
    fn test_row_polymorphism_with_lacks() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Function that requires a type WITHOUT certain fields
        // func processPublic<R: Lacks<password>>(
        //     obj: {name: String, ..R}
        // ) -> String
        // where R cannot have 'password' field
        
        let row_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("R".to_string()),
            ExprID(40),
        );
        
        // Add lacks constraint
        env.constrain(Constraint::Row {
            expr_id: ExprID(41),
            constraint: RowConstraint::Lacks {
                type_var: row_param.clone(),
                labels: BTreeSet::from(["password".to_string()]),
            },
        });
        
        // Create parameter type
        let param_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(42),
        );
        
        let mut base_fields = BTreeMap::new();
        base_fields.insert(
            "name".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(43),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(44),
            constraint: RowConstraint::HasRow {
                type_var: param_type.clone(),
                row: RowSpec { fields: base_fields },
                extension: Some(row_param.clone()),
            },
        });
        
        // Test with a safe type (no password field)
        let safe_user = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(50),
        );
        
        let mut safe_fields = BTreeMap::new();
        safe_fields.insert(
            "name".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(51),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        safe_fields.insert(
            "email".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(52),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(53),
            constraint: RowConstraint::HasExactRow {
                type_var: safe_user.clone(),
                row: RowSpec { fields: safe_fields },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test row polymorphism in higher-order functions
    #[test]
    fn test_row_polymorphism_higher_order() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Higher-order function that transforms records
        // func map<R1, R2>(
        //     transform: ({..R1}) -> {..R2},
        //     input: {..R1}
        // ) -> {..R2}
        
        let r1 = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("R1".to_string()),
            ExprID(60),
        );
        
        let r2 = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("R2".to_string()),
            ExprID(61),
        );
        
        // Input type has row R1
        let input_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(62),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(63),
            constraint: RowConstraint::HasRow {
                type_var: input_type.clone(),
                row: RowSpec { fields: BTreeMap::new() },
                extension: Some(r1.clone()),
            },
        });
        
        // Output type has row R2
        let output_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(64),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(65),
            constraint: RowConstraint::HasRow {
                type_var: output_type.clone(),
                row: RowSpec { fields: BTreeMap::new() },
                extension: Some(r2.clone()),
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test row polymorphism with concrete instantiation
    #[test]
    fn test_row_polymorphism_instantiation() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Simulating function instantiation
        // Generic: func first<R>(pair: {first: Int, second: Int, ..R}) -> Int
        // Instantiation: first({first: 1, second: 2, third: 3})
        
        // Generic row parameter
        let generic_r = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("R".to_string()),
            ExprID(70),
        );
        
        // Generic parameter type
        let generic_param = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(71),
        );
        
        let mut generic_fields = BTreeMap::new();
        generic_fields.insert(
            "first".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(72),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        generic_fields.insert(
            "second".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(73),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(74),
            constraint: RowConstraint::HasRow {
                type_var: generic_param.clone(),
                row: RowSpec { fields: generic_fields },
                extension: Some(generic_r.clone()),
            },
        });
        
        // Concrete type at call site
        let concrete_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(80),
        );
        
        let mut concrete_fields = BTreeMap::new();
        concrete_fields.insert(
            "first".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(81),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        concrete_fields.insert(
            "second".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(82),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        concrete_fields.insert(
            "third".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(83),
                metadata: FieldMetadata::RecordField {
                    index: 2,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(84),
            constraint: RowConstraint::HasExactRow {
                type_var: concrete_type.clone(),
                row: RowSpec { fields: concrete_fields },
            },
        });
        
        // Instantiated row variable (represents R = {third: Int})
        let instantiated_r = env.new_type_variable(
            TypeVarKind::Instantiated(1),
            ExprID(85),
        );
        
        let mut extra_fields = BTreeMap::new();
        extra_fields.insert(
            "third".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(86),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(87),
            constraint: RowConstraint::HasExactRow {
                type_var: instantiated_r.clone(),
                row: RowSpec { fields: extra_fields },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
}