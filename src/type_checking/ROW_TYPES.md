# Row-Based Type System

This document describes the row-based type system implementation based on qualified types from the papers by J. Garrett Morris et al.

## Overview

The row-based type system provides a more flexible and composable approach to extensible data types (structs, enums, protocols) by expressing type structure through constraints rather than embedding it directly in types.

### Key Concepts

1. **Qualified Types**: Row structure is expressed as constraints (qualifications) on type variables, not embedded in types
2. **Row Variables**: Type variables that represent collections of fields/members
3. **Row Constraints**: Constraints that specify what fields a row variable has
4. **Row Operations**: Concatenation, restriction, and subsumption of rows

## Architecture

### Core Types

- `RowConstraint` (in `row.rs`): Represents constraints on row variables
  - `HasField`: Specifies a single field
  - `HasRow`: Specifies multiple fields (open row)
  - `HasExactRow`: Specifies exactly these fields (closed row)
  - `RowConcat`: Row concatenation operation
  - `RowRestrict`: Row restriction operation
  - `Lacks`: Specifies fields that must NOT be present

- `FieldMetadata`: Metadata for different kinds of members
  - `RecordField`: Struct properties
  - `Method`: Type methods
  - `MethodRequirement`: Protocol requirements
  - `Initializer`: Constructors
  - `EnumVariant`: Enum variants

### Integration with TypeDef

TypeDef has been extended with:
- `row_var: Option<TypeVarID>`: Optional row variable for the type
- `ensure_row_var()`: Lazily creates a row variable when needed
- Row-aware methods: `add_properties_with_rows()`, etc.

### Constraint Solver Integration

The constraint solver checks row constraints when resolving member access:
1. First checks if a TypeDef has a row variable
2. If so, attempts to resolve through row constraints
3. Falls back to traditional member lookup

## Usage

### Creating Types with Rows

```rust
// Create a struct
let mut point_def = TypeDef {
    symbol_id: point_id,
    name_str: "Point".to_string(),
    kind: TypeDefKind::Struct,
    type_parameters: vec![],
    members: HashMap::new(),
    conformances: vec![],
    row_var: None, // Will be created automatically
};

// Register the type
env.register(&point_def).unwrap();

// Add properties using row-aware method
let properties = vec![
    Property::new(0, "x".to_string(), ExprID(1), Ty::Float, false),
    Property::new(1, "y".to_string(), ExprID(2), Ty::Float, false),
];

point_def.add_properties_with_rows(properties, &mut env);
```

### Gradual Migration

The system supports mixing traditional and row-based approaches:

```rust
// Add some members traditionally
rect_def.add_properties(vec![...]);

// Add others with rows
rect_def.add_properties_with_rows(vec![...], &mut env);
```

### Row Operations

```rust
// Row concatenation: combine two rows
env.constrain(Constraint::Row {
    expr_id: ExprID(1),
    constraint: RowConstraint::RowConcat {
        left: position_row,
        right: size_row,
        result: rect_row,
    },
});
```

## Benefits

1. **Cleaner Architecture**: No more repetitive pattern matching on TypeMember variants
2. **Composability**: Row operations enable clean type composition
3. **Flexibility**: Row polymorphism and extensible types are naturally supported
4. **Incremental Migration**: Can gradually adopt rows without breaking existing code

## Migration Strategy

1. **New Types**: Use row-aware methods (`add_properties_with_rows`, etc.)
2. **Existing Types**: Can continue using traditional methods
3. **Mixed Approach**: During migration, types can use both systems
4. **Testing**: Be aware that creating row variables changes type variable IDs

## Architecture Decision: Dual System

The implementation maintains both the HashMap and row constraints for the following reasons:

1. **Type Checking Phase**: Row constraints are the source of truth
   - Constraints are actively being solved
   - Type structure can be modified through row operations
   - Provides flexibility for qualified types

2. **Post-Type-Checking Phase**: HashMap provides efficient lookup
   - Used in lowering, code generation, LSP features
   - Contains the resolved type information
   - Avoids needing to traverse constraints repeatedly

3. **Synchronization**: Row-aware methods update both systems
   - Ensures consistency between representations
   - Allows gradual migration without breaking existing code

## Implementation Status

- [x] Row type definitions and constraints
- [x] Integration with constraint solver
- [x] Row operations (concatenation, restriction)
- [x] TypeDef integration with backwards compatibility
- [x] Row-aware member addition methods
- [x] Comprehensive test suite
- [ ] Automatic migration disabled to avoid breaking tests

## Future Work

- Row subsumption for more advanced type relationships
- Syntactic sugar for row type declarations
- Performance optimizations for row constraint solving
- Full migration of existing code when appropriate