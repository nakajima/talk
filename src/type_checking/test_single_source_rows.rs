#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    
    use crate::{
        SymbolID,
        ExprMetaStorage,
        environment::Environment,
        expr_id::ExprID,
        type_def::{TypeDef, TypeDefKind, Property},
        ty::Ty,
    };
    
    #[test]
    fn test_single_source_row_system() {
        let mut env = Environment::default();
        let meta = ExprMetaStorage::default();
        
        // Create a struct type
        let struct_id = SymbolID(1000);
        let mut struct_def = TypeDef {
            symbol_id: struct_id,
            name_str: "Point".to_string(),
            kind: TypeDefKind::Struct,
            type_parameters: vec![],
            members: HashMap::new(),
            conformances: vec![],
            row_var: None,
        };
        
        // Register the type
        env.register(&struct_def).unwrap();
        
        // Add properties using row-aware method (should NOT populate members)
        let properties = vec![
            Property::new(0, "x".to_string(), ExprID(1), Ty::Float, false),
            Property::new(1, "y".to_string(), ExprID(2), Ty::Float, false),
        ];
        
        struct_def.add_properties_with_rows(properties, &mut env);
        
        // At this point, members should still be empty
        assert!(struct_def.members.is_empty(), "Members should be empty before constraint solving");
        
        // Update the type in environment
        env.types.insert(struct_id, struct_def);
        
        // Run constraint solving
        let solution = env.flush_constraints(&meta).unwrap();
        assert!(solution.errors.is_empty());
        
        // Now members should be populated
        let struct_def = env.lookup_type(&struct_id).unwrap();
        assert_eq!(struct_def.members.len(), 2, "Members should be populated after constraint solving");
        
        // Verify the properties are correct
        let x_prop = struct_def.find_property("x").unwrap();
        assert_eq!(x_prop.name, "x");
        assert_eq!(x_prop.ty, Ty::Float);
        assert_eq!(x_prop.index, 0);
        
        let y_prop = struct_def.find_property("y").unwrap();
        assert_eq!(y_prop.name, "y");
        assert_eq!(y_prop.ty, Ty::Float);
        assert_eq!(y_prop.index, 1);
    }
    
    #[test]
    fn test_row_constraints_are_source_of_truth() {
        let mut env = Environment::default();
        let meta = ExprMetaStorage::default();
        
        // Create a struct
        let struct_id = SymbolID(2000);
        let mut struct_def = TypeDef {
            symbol_id: struct_id,
            name_str: "Rectangle".to_string(),
            kind: TypeDefKind::Struct,
            type_parameters: vec![],
            members: HashMap::new(),
            conformances: vec![],
            row_var: None,
        };
        
        env.register(&struct_def).unwrap();
        
        // Add properties via row constraints only
        struct_def.add_properties_with_rows(
            vec![
                Property::new(0, "width".to_string(), ExprID(10), Ty::Float, false),
                Property::new(1, "height".to_string(), ExprID(11), Ty::Float, false),
            ],
            &mut env,
        );
        
        // Manually add a bogus member to the HashMap (this should be overwritten)
        struct_def.members.insert(
            "bogus".to_string(),
            crate::type_def::TypeMember::Property(Property::new(
                99,
                "bogus".to_string(),
                ExprID(99),
                Ty::string(),
                false,
            )),
        );
        
        env.types.insert(struct_id, struct_def);
        
        // Solve constraints - this should repopulate members from rows
        env.flush_constraints(&meta).unwrap();
        
        // Verify that only the row-based properties exist
        let struct_def = env.lookup_type(&struct_id).unwrap();
        assert_eq!(struct_def.members.len(), 2);
        assert!(struct_def.find_property("width").is_some());
        assert!(struct_def.find_property("height").is_some());
        assert!(struct_def.find_property("bogus").is_none(), "Bogus member should be removed");
    }
}