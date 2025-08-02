# Plan: Basic Type Definition Storage and Lookup

## Goal
Implement a minimal type definition storage system that bridges between the old TypeDef system and the new constraint-based Row types, so that lookup_type(), lookup_struct(), lookup_enum(), and lookup_protocol() can return actual TypeDef instances.

## Current Situation
- All lookup methods return None (stubbed)
- Tests expect TypeDef instances with members, variants, etc.
- We have Row types with constraints, but no way to convert them back to TypeDef
- No storage mechanism for type definitions

## Proposed Solution

### Option 1: Dual Storage (Recommended for Migration)
Store both TypeDef AND Row representations temporarily:
```rust
struct Environment {
    // ... existing fields ...
    
    // NEW: Store TypeDefs indexed by SymbolID
    type_definitions: BTreeMap<SymbolID, TypeDef>,
    
    // NEW: Map SymbolIDs to their Row type representations
    type_rows: BTreeMap<SymbolID, Ty>,  // Where Ty is always Ty::Row
}
```

**Pros:**
- Tests continue to work with minimal changes
- Can migrate incrementally
- Easy rollback if needed

**Cons:**
- Duplication of data
- Need to keep both in sync

### Option 2: Generate TypeDef from Constraints On-Demand
When lookup_type() is called:
1. Find the Row type by SymbolID
2. Extract constraints for that type
3. Build a TypeDef from the constraints
4. Return the generated TypeDef

**Pros:**
- Single source of truth (constraints)
- No duplication

**Cons:**
- More complex
- Performance overhead on every lookup
- Need to fully implement constraint → TypeDef conversion

### Option 3: Replace TypeDef Completely
Don't return TypeDef at all - change all consumers to work with Row types directly.

**Pros:**
- Cleanest long-term solution
- No bridging needed

**Cons:**
- Massive refactoring
- All tests need rewriting
- Too big for incremental approach

## Recommended Approach: Option 1 (Dual Storage)

### Implementation Steps

#### Step 1: Add Storage Fields to Environment
```rust
// In environment.rs
pub struct Environment {
    // ... existing fields ...
    
    /// Storage for type definitions (temporary during migration)
    type_definitions: BTreeMap<SymbolID, TypeDef>,
    
    /// Storage for row type representations
    type_rows: BTreeMap<SymbolID, Ty>,
}
```

#### Step 2: Update register() Method
```rust
pub fn register(&mut self, type_def: &TypeDef) -> Result<(), TypeError> {
    let symbol_id = type_def.symbol_id;
    
    // Store the TypeDef
    self.type_definitions.insert(symbol_id, type_def.clone());
    
    // Create and store corresponding Row type
    let row_type = self.create_row_from_typedef(type_def)?;
    self.type_rows.insert(symbol_id, row_type);
    
    Ok(())
}
```

#### Step 3: Implement create_row_from_typedef()
```rust
fn create_row_from_typedef(&mut self, type_def: &TypeDef) -> Result<Ty, TypeError> {
    let type_var = self.new_type_variable(TypeVarKind::Row, ExprID(0));
    let mut constraints = vec![];
    
    // Convert members to constraints
    for (name, member) in &type_def.members {
        match member {
            TypeMember::Property(prop) => {
                constraints.push(RowConstraint::HasField {
                    type_var: type_var.clone(),
                    label: name.clone(),
                    field_ty: prop.ty.clone(),
                    metadata: FieldMetadata::RecordField {
                        index: prop.index,
                        has_default: prop.default_value.is_some(),
                        is_mutable: prop.is_mutable,
                    },
                });
            }
            TypeMember::Variant(variant) => {
                constraints.push(RowConstraint::HasField {
                    type_var: type_var.clone(),
                    label: name.clone(),
                    field_ty: variant.ty.clone(),
                    metadata: FieldMetadata::EnumCase {
                        tag: variant.tag as usize,
                    },
                });
            }
            TypeMember::Method(method) => {
                constraints.push(RowConstraint::HasField {
                    type_var: type_var.clone(),
                    label: name.clone(),
                    field_ty: method.ty.clone(),
                    metadata: FieldMetadata::Method,
                });
            }
            // ... handle other member types
        }
    }
    
    // Determine RowKind based on TypeDefKind
    let kind = match type_def.kind {
        TypeDefKind::Struct => RowKind::Struct(symbol_id, type_def.name.clone()),
        TypeDefKind::Enum => RowKind::Enum(symbol_id, type_def.name.clone()),
        TypeDefKind::Protocol => RowKind::Protocol(symbol_id, type_def.name.clone()),
    };
    
    Ok(Ty::Row {
        type_var,
        constraints,
        generics: vec![], // TODO: Handle generics
        kind,
    })
}
```

#### Step 4: Update Lookup Methods
```rust
pub fn lookup_type(&self, id: &SymbolID) -> Option<TypeDef> {
    self.type_definitions.get(id).cloned()
}

pub fn lookup_struct(&self, id: &SymbolID) -> Option<TypeDef> {
    self.type_definitions.get(id)
        .filter(|td| matches!(td.kind, TypeDefKind::Struct))
        .cloned()
}

pub fn lookup_enum(&self, id: &SymbolID) -> Option<TypeDef> {
    self.type_definitions.get(id)
        .filter(|td| matches!(td.kind, TypeDefKind::Enum))
        .cloned()
}

pub fn lookup_protocol(&self, id: &SymbolID) -> Option<TypeDef> {
    self.type_definitions.get(id)
        .filter(|td| matches!(td.kind, TypeDefKind::Protocol))
        .cloned()
}
```

#### Step 5: Handle Type Hoisting
When types are created during hoisting (type_checker_hoisting.rs), we need to:
1. Create the Row type with constraints
2. Create a corresponding TypeDef
3. Store both in Environment

```rust
// In type_checker_hoisting.rs, after building the Row type:
let type_def = self.create_typedef_from_row(&row_type, symbol_id, &spec)?;
env.register(&type_def)?;
```

## Benefits of This Approach

1. **Tests will start passing immediately** - As soon as we store TypeDefs, lookup methods will return real data
2. **Incremental migration** - We can gradually move code from TypeDef to constraints
3. **Debugging aid** - Can compare TypeDef and Row representations to ensure correctness
4. **Rollback safety** - If something breaks, we still have the TypeDef data

## Testing Strategy

1. Start with simple struct registration and lookup
2. Add enum variant support
3. Add protocol member support
4. Verify that existing tests pass
5. Add tests for constraint-based operations

## Migration Path

1. **Phase 1** (Current): Dual storage, tests pass
2. **Phase 2**: Start using Row types internally, keep TypeDef for API
3. **Phase 3**: Migrate consumers to use Row types directly
4. **Phase 4**: Remove TypeDef storage entirely

## Files to Modify

1. `src/type_checking/environment.rs` - Add storage, update methods
2. `src/type_checking/type_checker_hoisting.rs` - Create and register TypeDefs
3. `src/type_checking/type_def.rs` - Add conversion methods if needed

## Risks and Mitigations

**Risk**: Data gets out of sync between TypeDef and Row
**Mitigation**: Always update both through register() method

**Risk**: Performance overhead of dual storage
**Mitigation**: This is temporary; optimize after migration complete

**Risk**: Complex conversion logic
**Mitigation**: Start simple, add complexity incrementally

## Success Criteria

- [ ] lookup_type() returns actual TypeDef instances
- [ ] Tests that call lookup methods no longer panic
- [ ] At least 50% more tests pass
- [ ] Can register and retrieve structs, enums, and protocols