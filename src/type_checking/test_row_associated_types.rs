//! Test row-based associated types for protocols

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
    
    /// Test that protocols can define associated types as row constraints
    #[test]
    fn test_protocol_with_row_associated_type() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a protocol with an associated type defined via row constraints
        // protocol Container<ElementRow> {
        //     // ElementRow is a row variable representing the element's structure
        //     func get() -> { ..ElementRow }
        // }
        
        let _protocol_id = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Container".to_string()),
            ExprID(1),
        );
        
        // The associated type is a row variable
        let element_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("ElementRow".to_string()),
            ExprID(2),
        );
        
        // Define that the protocol's get method returns a type with the element row
        let return_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(3),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(4),
            constraint: RowConstraint::HasRow {
                type_var: return_type.clone(),
                row: RowSpec { fields: BTreeMap::new() }, // Empty initially
                extension: Some(element_row.clone()), // Extended by ElementRow
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test conformance with concrete row for associated type
    #[test]
    fn test_conformance_with_concrete_row() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a type that conforms to Container with a specific row
        // struct PointContainer: Container<{x: Int, y: Int}> {
        //     func get() -> {x: Int, y: Int}
        // }
        
        let _point_container = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("PointContainer".to_string()),
            ExprID(10),
        );
        
        // Define the concrete row for the associated type
        let point_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("PointRow".to_string()),
            ExprID(11),
        );
        
        let mut fields = BTreeMap::new();
        fields.insert(
            "x".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(12),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        fields.insert(
            "y".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(13),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(14),
            constraint: RowConstraint::HasExactRow {
                type_var: point_row.clone(),
                row: RowSpec { fields },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test generic conformance with row variable for associated type
    #[test]
    fn test_generic_conformance_with_row_variable() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Create a generic type that forwards its row to the protocol
        // struct GenericContainer<R>: Container<R> {
        //     func get() -> { ..R }
        // }
        
        let _generic_container = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("GenericContainer".to_string()),
            ExprID(20),
        );
        
        let row_param = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("R".to_string()),
            ExprID(21),
        );
        
        // The return type of get() has row R
        let return_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(22),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(23),
            constraint: RowConstraint::HasRow {
                type_var: return_type.clone(),
                row: RowSpec { fields: BTreeMap::new() },
                extension: Some(row_param.clone()),
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test row composition with associated types
    #[test]
    fn test_row_composition_with_associated_types() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Test composing rows for associated types
        // protocol Identifiable<IdRow> { ... }
        // protocol Timestamped<TimeRow> { ... }
        // struct Document<D>: Identifiable<{id: String}>, Timestamped<{created: Int, updated: Int}> 
        //   where D = {id: String, created: Int, updated: Int, ...}
        
        let _document = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Document".to_string()),
            ExprID(30),
        );
        
        // Create the ID row
        let id_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("IdRow".to_string()),
            ExprID(31),
        );
        
        let mut id_fields = BTreeMap::new();
        id_fields.insert(
            "id".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(32),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(33),
            constraint: RowConstraint::HasRow {
                type_var: id_row.clone(),
                row: RowSpec { fields: id_fields },
                extension: None,
            },
        });
        
        // Create the time row
        let time_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("TimeRow".to_string()),
            ExprID(34),
        );
        
        let mut time_fields = BTreeMap::new();
        time_fields.insert(
            "created".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(35),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        time_fields.insert(
            "updated".to_string(),
            FieldInfo {
                ty: Ty::Int,
                expr_id: ExprID(36),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(37),
            constraint: RowConstraint::HasRow {
                type_var: time_row.clone(),
                row: RowSpec { fields: time_fields },
                extension: None,
            },
        });
        
        // Compose the rows for the document type
        let doc_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("DocRow".to_string()),
            ExprID(38),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(39),
            constraint: RowConstraint::RowConcat {
                left: id_row.clone(),
                right: time_row.clone(),
                result: doc_row.clone(),
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
    
    /// Test row constraints on protocol method parameters
    #[test]
    fn test_row_constraints_on_protocol_methods() {
        let mut env = Environment::new();
        let meta = ExprMetaStorage::default();
        
        // Protocol with row constraints on method parameters
        // protocol Processor<InputRow, OutputRow> {
        //     func process(input: {..InputRow}) -> {..OutputRow}
        // }
        
        let _processor = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("Processor".to_string()),
            ExprID(40),
        );
        
        let input_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("InputRow".to_string()),
            ExprID(41),
        );
        
        let output_row = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("OutputRow".to_string()),
            ExprID(42),
        );
        
        // Create types with these row constraints
        let input_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(43),
        );
        
        let output_type = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(44),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(45),
            constraint: RowConstraint::HasRow {
                type_var: input_type.clone(),
                row: RowSpec { fields: BTreeMap::new() },
                extension: Some(input_row.clone()),
            },
        });
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(46),
            constraint: RowConstraint::HasRow {
                type_var: output_type.clone(),
                row: RowSpec { fields: BTreeMap::new() },
                extension: Some(output_row.clone()),
            },
        });
        
        // Test a concrete implementation
        let _name_processor = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter("NameProcessor".to_string()),
            ExprID(47),
        );
        
        // Define concrete rows for the implementation
        let mut input_fields = BTreeMap::new();
        input_fields.insert(
            "firstName".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(48),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        input_fields.insert(
            "lastName".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(49),
                metadata: FieldMetadata::RecordField {
                    index: 1,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        let concrete_input = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(50),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(51),
            constraint: RowConstraint::HasExactRow {
                type_var: concrete_input.clone(),
                row: RowSpec { fields: input_fields },
            },
        });
        
        let mut output_fields = BTreeMap::new();
        output_fields.insert(
            "fullName".to_string(),
            FieldInfo {
                ty: Ty::string(),
                expr_id: ExprID(52),
                metadata: FieldMetadata::RecordField {
                    index: 0,
                    has_default: false,
                    is_mutable: false,
                },
            },
        );
        
        let concrete_output = env.new_type_variable(
            TypeVarKind::Let,
            ExprID(53),
        );
        
        env.constrain(Constraint::Row {
            expr_id: ExprID(54),
            constraint: RowConstraint::HasExactRow {
                type_var: concrete_output.clone(),
                row: RowSpec { fields: output_fields },
            },
        });
        
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
    }
}