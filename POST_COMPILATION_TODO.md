# Post-Compilation TODO: Row Type Refactoring

## Status
✅ **All compilation errors fixed!** The main codebase compiles successfully with the new constraint-based row type system.

## What We Changed
- `Ty::Row` now stores constraints instead of fields directly
- Row structure is expressed through constraints on type variables
- Added helper methods for field access from constraints
- Converted all primitive types to `Ty::Primitive(Primitive::X)`
- Stubbed out type definition lookups

## Remaining Work

### 1. Fix Test Compilation (43 errors)
**Priority: HIGH**
- Tests are still using old `Ty::Bool`, `Ty::Int`, `Ty::Float` instead of `Ty::Primitive(Primitive::X)`
- Tests expect old Row structure with `fields` and `row` fields
- Tests use stubbed lookup methods that now return None

**Action items:**
- [ ] Update all test assertions to use `Ty::Primitive(Primitive::Bool)` etc.
- [ ] Update tests that create Row types to use constraints
- [ ] Fix tests that rely on lookup_struct/lookup_enum/lookup_protocol
- [ ] Update pattern matching tests for new Row structure

### 2. Implement Proper Constraint-Based Lookups
**Priority: HIGH**
Currently stubbed as returning None:
- `Environment::lookup_enum()`
- `Environment::lookup_struct()` 
- `Environment::lookup_protocol()`
- `Environment::lookup_type()`

**Action items:**
- [ ] Design how to retrieve type definitions from row constraints
- [ ] Implement constraint-based type definition resolution
- [ ] Create a TypeDef from row constraints when needed
- [ ] Handle generic type parameters in constraint-based lookups

### 3. Complete Row Constraint Implementation
**Priority: HIGH**

#### Currently stubbed/incomplete:
- Enum variant resolution from constraints
- Struct property resolution from constraints  
- Protocol member resolution from constraints
- Row variable handling in record types

**Action items:**
- [ ] Implement enum variant lookup from `HasField` constraints with `EnumCase` metadata
- [ ] Implement struct property indexing from `RecordField` metadata
- [ ] Implement protocol conformance checking with constraints
- [ ] Handle row extensions properly (currently commented out)

### 4. Fix TypeDef Integration
**Priority: MEDIUM**

The old TypeDef system is disconnected from the new constraint-based system:
- TypeDef still expects to store members directly
- Need to populate TypeDef from row constraints
- Monomorphizer returns None for all type lookups

**Action items:**
- [ ] Create TypeDef instances from row constraints when needed
- [ ] Update TypeDef::populate_from_rows() to work with new system
- [ ] Fix monomorphizer to work with constraint-based types
- [ ] Update driver.rs to collect types from constraints

### 5. Complete Row Operations
**Priority: MEDIUM**

Several row operations are incomplete:
- Row concatenation (RowConcat constraint)
- Row restriction (RowRestrict constraint)
- Row extension tracking
- Row variable unification

**Action items:**
- [ ] Implement RowConcat constraint solving
- [ ] Implement RowRestrict constraint solving
- [ ] Track row extensions in HasRow constraints
- [ ] Handle row variable substitution properly

### 6. Fix LSP Completions
**Priority: LOW**

LSP completions rely on TypeDef lookups which now return None:
- Member completions don't work
- Type completions are broken

**Action items:**
- [ ] Update completion provider to get members from row constraints
- [ ] Implement field completion from HasField constraints
- [ ] Fix method completion from Method metadata

### 7. Update Error Messages
**Priority: LOW**

Error messages still reference old terminology:
- "fields" instead of "constraints"
- Missing field errors don't check constraints
- Type mismatch errors don't show constraint information

**Action items:**
- [ ] Update error messages to reference constraints
- [ ] Improve constraint-related error reporting
- [ ] Add constraint information to type mismatch errors

### 8. Performance Optimization
**Priority: LOW**

Current implementation may have performance issues:
- Constraints are duplicated across Row instances
- Field lookups iterate through all constraints
- No caching of extracted fields

**Action items:**
- [ ] Consider constraint interning/pooling
- [ ] Cache extracted fields in Row types
- [ ] Profile and optimize hot paths
- [ ] Consider indexing constraints by label

### 9. Documentation
**Priority: LOW**

The new system needs documentation:
- How constraints represent row structure
- How to work with the new Row types
- Migration guide from old to new system

**Action items:**
- [ ] Document the constraint-based type system
- [ ] Add examples of creating and using Row types
- [ ] Document helper methods and their usage
- [ ] Create architecture documentation

### 10. Clean Up Dead Code
**Priority: LOW**

Remove old code that's no longer needed:
- Old TypeDef system (if fully replaced)
- Commented-out code from migration
- Stub implementations that are no longer needed

**Action items:**
- [ ] Remove old TypeDef code if fully replaced
- [ ] Clean up TODO comments
- [ ] Remove stub implementations once replaced
- [ ] Delete migration artifacts

## Testing Strategy

1. **Get tests compiling** - Update syntax and structure
2. **Get tests passing** - Implement missing functionality
3. **Add new tests** - Cover constraint-based features
4. **Integration tests** - Ensure system works end-to-end

## Next Steps (Recommended Order)

1. **Fix test compilation** - Can't validate anything until tests run
2. **Implement basic lookups** - Get lookup_struct/enum working minimally
3. **Fix enum variants** - Critical for pattern matching
4. **Fix struct properties** - Critical for field access
5. **Complete row operations** - For full row polymorphism
6. **Everything else** - LSP, optimization, cleanup

## Key Files to Focus On

### High Priority
- `src/type_checking/type_checker_tests.rs` - Fix test compilation
- `src/type_checking/environment.rs` - Implement lookups
- `src/type_checking/constraint_solver.rs` - Complete constraint solving
- `src/type_checking/row_constraints.rs` - Implement row operations

### Medium Priority  
- `src/type_checking/type_def.rs` - Integrate with constraints
- `src/transforms/monomorphizer.rs` - Fix type lookups
- `src/lowering/lowerer.rs` - Complete field access generation

### Low Priority
- `src/lsp/completion.rs` - Fix completions
- `src/compiling/driver.rs` - Collect types properly

## Success Criteria

- [ ] All tests compile and pass
- [ ] Enum pattern matching works
- [ ] Struct field access works
- [ ] Protocol conformance works
- [ ] Row polymorphism works
- [ ] No stub implementations remain
- [ ] Performance is acceptable