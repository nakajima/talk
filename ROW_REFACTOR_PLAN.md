# Row Type Refactoring Plan

## Overview
Refactoring the type system from storing fields directly in `Ty::Row` to using a constraint-based approach where row structure is expressed through constraints on type variables.

## Current Status
- ✅ `Ty::Row` refactored to use `type_var: TypeVarID` instead of `fields: BTreeMap<String, FieldInfo>`
- ❌ 113 compilation errors across the codebase
- Most errors are due to code expecting direct field access

## Error Analysis
- 37 E0599 errors (missing methods like `lookup_type`, `lookup_enum`, etc.)
- 31 E0308 errors (type mismatches)
- 13 E0026 errors (variant field access)
- 12 E0559 errors (wrong number of arguments)

## Most Affected Files
1. `src/type_checking/ty.rs` - 36 errors
2. `src/type_checking/constraint_solver.rs` - 35 errors
3. `src/lowering/lowerer.rs` - 24 errors
4. `src/type_checking/type_checker.rs` - 11 errors
5. `src/type_checking/environment.rs` - 11 errors

## Implementation Plan

### Phase 1: Core Infrastructure
**Goal**: Add helper methods to work with the new constraint-based system
- [ ] Create methods to look up fields from row constraints for a given type variable
- [ ] Add utilities to extract field information from `RowConstraint`s
- [ ] Build a bridge between the old field-access patterns and new constraint system
- [ ] Add a `ConstraintContext` or similar to pass constraint information where needed

### Phase 2: Environment Updates
**Goal**: Fix the Environment to support constraint-based lookups
- [ ] Add methods to query row constraints for a type variable
- [ ] Create methods to get all fields for a Row type by examining its constraints
- [ ] Replace the old `lookup_type`, `lookup_enum`, `lookup_struct` with constraint-based alternatives
- [ ] Add a constraint store/index for efficient lookups

### Phase 3: Type System Core (ty.rs - 36 errors)
**Goal**: Fix the core type system issues
- [ ] Update type comparison methods (`satisfies`, `equal_to`) to work with constraints
- [ ] Fix pattern matching on `Ty::Row` throughout
- [ ] Update any direct field access to use constraint lookups
- [ ] Fix type substitution and replacement methods

### Phase 4: Constraint Solver (35 errors)
**Goal**: Update member resolution in the constraint solver
- [ ] Replace type definition lookups with constraint-based field resolution
- [ ] Update member type resolution to query row constraints
- [ ] Fix builtin type member access
- [ ] Update method resolution to use constraints

### Phase 5: Code Generation (lowerer.rs - 24 errors)
**Goal**: Update the lowerer to generate correct code
- [ ] Fix record literal compilation to get fields from constraints
- [ ] Update field access code generation
- [ ] Fix struct/enum construction
- [ ] Update pattern matching compilation
- [ ] Fix member access lowering

### Phase 6: Type Checker (18 errors)
**Goal**: Update type checking and hoisting
- [ ] Fix type hoisting to create proper row constraints
- [ ] Update method resolution
- [ ] Fix type definition creation
- [ ] Update conformance checking

### Phase 7: Supporting Modules
**Goal**: Fix remaining modules
- [ ] Pattern exhaustiveness checking
- [ ] LSP completions
- [ ] Monomorphizer
- [ ] Various analysis passes
- [ ] Definite initialization analysis

### Phase 8: Testing & Validation
**Goal**: Ensure the system works correctly
- [ ] Run tests to identify runtime issues
- [ ] Fix any semantic problems that arise
- [ ] Ensure the constraint-based system works end-to-end
- [ ] Add tests for the new constraint-based row system

## Key Considerations

1. **Backward Compatibility**: Some code may still need to work with the old TypeDef system during the transition
2. **Performance**: Constraint lookups may be slower than direct field access - consider caching
3. **Error Messages**: Update error messages to be meaningful in the constraint-based system
4. **Documentation**: Document the new constraint-based approach for future maintainers

## Next Steps
1. Start with Phase 1 - build the infrastructure for constraint lookups
2. Focus on getting a minimal path compiling first
3. Incrementally fix modules, starting with the most critical ones