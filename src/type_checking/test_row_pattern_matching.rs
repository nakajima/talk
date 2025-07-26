//! Test row-based pattern matching for enums with exhaustiveness checking

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
    use std::collections::BTreeMap;
    
    /// Test basic enum pattern matching with row-based variants
    #[test]
    fn test_basic_enum_pattern_matching() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create an enum type with row-based variants
        // enum Result<T, E> = Ok(T) | Err(E)
        
        let result_enum = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Result".to_string()),
            ExprID(1),
        );
        
        let t_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("T".to_string()),
            ExprID(2),
        );
        
        let e_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("E".to_string()),
            ExprID(3),
        );
        
        // Define Ok variant through row constraints
        let mut ok_fields = BTreeMap::new();
        ok_fields.insert(
            "Ok".to_string(),
            FieldInfo {
                ty: Ty::TypeVar(t_param.clone()),
                expr_id: ExprID(4),
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        );
        
        // Define Err variant through row constraints
        let mut err_fields = BTreeMap::new();
        err_fields.insert(
            "Err".to_string(),
            FieldInfo {
                ty: Ty::TypeVar(e_param.clone()),
                expr_id: ExprID(5),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        );
        
        // Add both variants to the enum
        env.constrain(Constraint::Row {
            expr_id: ExprID(6),
            constraint: RowConstraint::HasField {
                type_var: result_enum.clone(),
                label: "Ok".to_string(),
                field_ty: Ty::TypeVar(t_param.clone()),
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(7),
            constraint: RowConstraint::HasField {
                type_var: result_enum.clone(),
                label: "Err".to_string(),
                field_ty: Ty::TypeVar(e_param.clone()),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test exhaustiveness checking for row-based enums
    #[test]
    fn test_exhaustiveness_with_row_variants() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create an enum with exactly known variants (exact row)
        // enum Color = Red | Green | Blue
        
        let color_enum = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Color".to_string()),
            ExprID(10),
        );
        
        let mut color_fields = BTreeMap::new();
        
        color_fields.insert(
            "Red".to_string(),
            FieldInfo {
                ty: Ty::Void,
                expr_id: ExprID(11),
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        );
        
        color_fields.insert(
            "Green".to_string(),
            FieldInfo {
                ty: Ty::Void,
                expr_id: ExprID(12),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        );
        
        color_fields.insert(
            "Blue".to_string(),
            FieldInfo {
                ty: Ty::Void,
                expr_id: ExprID(13),
                metadata: FieldMetadata::EnumCase { tag: 2 },
            },
        );
        
        // Use HasExactRow to ensure no additional variants
        env.constrain(Constraint::Row {
            expr_id: ExprID(14),
            constraint: RowConstraint::HasExactRow {
                type_var: color_enum.clone(),
                row: RowSpec { fields: color_fields },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test open vs closed enums for exhaustiveness
    #[test]
    fn test_open_vs_closed_enum_exhaustiveness() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Closed enum (exact row) - can be exhaustively matched
        let closed_enum = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("ClosedEnum".to_string()),
            ExprID(20),
        );
        
        let mut closed_fields = BTreeMap::new();
        closed_fields.insert(
            "A".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(21),
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        );
        closed_fields.insert(
            "B".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(22),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(23),
            constraint: RowConstraint::HasExactRow {
                type_var: closed_enum.clone(),
                row: RowSpec { fields: closed_fields },
            },
        });
        
        // Open enum (extensible row) - cannot be exhaustively matched without wildcard
        let open_enum = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("OpenEnum".to_string()),
            ExprID(24),
        );
        
        let extension_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("R".to_string()),
            ExprID(25),
        );
        
        let mut base_fields = BTreeMap::new();
        base_fields.insert(
            "X".to_string(),
            FieldInfo {
                ty: Ty::Bool,
                expr_id: ExprID(26),
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        );
        base_fields.insert(
            "Y".to_string(),
            FieldInfo {
                ty: Ty::Float,
                expr_id: ExprID(27),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(28),
            constraint: RowConstraint::HasRow {
                type_var: open_enum.clone(),
                row: RowSpec { fields: base_fields },
                extension: Some(extension_row.clone()),
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test pattern matching with variant payloads
    #[test]
    fn test_pattern_matching_variant_payloads() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // enum Message = Text(String) | Number(Int) | Pair(Int, String)
        
        let message_enum = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Message".to_string()),
            ExprID(30),
        );
        
        let mut message_fields = BTreeMap::new();
        
        // Text variant with String payload
        message_fields.insert(
            "Text".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(31),
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        );
        
        // Number variant with Int payload
        message_fields.insert(
            "Number".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(32),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        );
        
        // Pair variant with tuple payload
        message_fields.insert(
            "Pair".to_string(),
            FieldInfo {
                ty: Ty::Tuple(vec![Ty::Int, Ty::string()]),
                expr_id: ExprID(33),
                metadata: FieldMetadata::EnumCase { tag: 2 },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(34),
            constraint: RowConstraint::HasExactRow {
                type_var: message_enum.clone(),
                row: RowSpec { fields: message_fields },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test nested pattern matching with row-based enums
    #[test]
    fn test_nested_pattern_matching() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Option<Result<T, E>>
        
        // First create Result<T, E>
        let result_enum = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Result".to_string()),
            ExprID(40),
        );
        
        let t_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("T".to_string()),
            ExprID(41),
        );
        
        let e_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("E".to_string()),
            ExprID(42),
        );
        
        let mut result_fields = BTreeMap::new();
        result_fields.insert(
            "Ok".to_string(),
            FieldInfo {
                ty: Ty::TypeVar(t_param.clone()),
                expr_id: ExprID(43),
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        );
        result_fields.insert(
            "Err".to_string(),
            FieldInfo {
                ty: Ty::TypeVar(e_param.clone()),
                expr_id: ExprID(44),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(45),
            constraint: RowConstraint::HasExactRow {
                type_var: result_enum.clone(),
                row: RowSpec { fields: result_fields },
            },
        });
        
        // Now create Option<Result<T, E>>
        let option_enum = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Option".to_string()),
            ExprID(46),
        );
        
        let inner_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Inner".to_string()),
            ExprID(47),
        );
        
        let mut option_fields = BTreeMap::new();
        option_fields.insert(
            "Some".to_string(),
            FieldInfo {
                ty: Ty::TypeVar(inner_param.clone()),
                expr_id: ExprID(48),
                metadata: FieldMetadata::EnumCase { tag: 0 },
            },
        );
        option_fields.insert(
            "None".to_string(),
            FieldInfo {
                ty: Ty::Void,
                expr_id: ExprID(49),
                metadata: FieldMetadata::EnumCase { tag: 1 },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(50),
            constraint: RowConstraint::HasExactRow {
                type_var: option_enum.clone(),
                row: RowSpec { fields: option_fields },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
}