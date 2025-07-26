# Row-Based Constraint Migration Plan

## Overview

This document outlines the plan for migrating from traditional constraints (MemberAccess, ConformsTo, etc.) to row-based constraints in the Talk type system.

## Current State

1. **MemberAccess Constraint**: Currently handles member access like `obj.field`
2. **Row Constraints**: Already implemented and working for TypeVars
3. **Dual System**: TypeDef maintains both HashMap and row variables

## Challenges Discovered

1. **Struct/Enum Type Linkage**: When we have `Ty::Struct(id, generics)`, the constraint solver doesn't know to check the struct's row variable
2. **Backward Compatibility**: Many tests depend on the current MemberAccess resolution
3. **Builtin Types**: Need special handling for Int, Float, Bool, etc.

## Migration Strategy

### Phase 1: Foundation (Current)
- ✅ Row constraint infrastructure exists
- ✅ TypeDef has row_var support
- ✅ Row constraints work for TypeVars
- ✅ populate_from_rows syncs HashMap from row constraints

### Phase 2: Dual Operation
Instead of replacing constraints immediately:
1. Keep generating MemberAccess constraints
2. Also generate row constraints in parallel
3. Constraint solver can use either path

### Phase 3: Gradual Migration
1. **MemberAccess**: 
   - For TypeVars: Already checks row constraints
   - For Struct/Enum: Add fallback to check row_var
   - Eventually remove MemberAccess entirely

2. **ConformsTo**:
   - Protocol conformance = "has at least these members"
   - Use HasRow with extension variable
   - Protocol methods become row fields

3. **VariantMatch**:
   - Enum variants are already row fields
   - Convert to HasField constraints

4. **InitializerCall**:
   - Initializers are methods with special metadata
   - Use HasField with FieldMetadata::Initializer

### Phase 4: Full Migration
1. Remove old constraint variants
2. Update all tests
3. Remove HashMap from TypeDef (keep only for performance in post-type-checking phases)

## Implementation Notes

### Key Insight
The qualified types approach means that type structure is expressed through constraints, not embedded in types. A struct type is just an identifier - its members come from row constraints.

### Technical Approach
1. When creating MemberAccess for `Struct(id, generics).member`:
   - Get or create the struct's row_var
   - Add `HasField { type_var: row_var, label: member, ... }`
   - Optionally add constraint linking struct type to row var

2. Modify constraint solver's resolve_type_member:
   - Check if type has row_var
   - If so, check row constraints for that var
   - Fall back to HashMap for compatibility

## Benefits of Row-Based Approach

1. **Composability**: Row operations (concat, restrict) enable clean type composition
2. **Flexibility**: Row polymorphism and extensible records
3. **Uniformity**: All member-like operations use the same mechanism
4. **Simplification**: No more special cases for different constraint types

## Next Steps

1. Implement Phase 2: Add row constraints alongside existing constraints
2. Update constraint solver to check row_var for struct/enum types
3. Gradually migrate each constraint type
4. Update tests incrementally
5. Eventually remove old constraint types