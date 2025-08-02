# V2 Interpreter TODO

## Current Status

The v2 interpreter has made significant progress and now supports:
- ✅ Basic arithmetic and comparisons
- ✅ Function calls and recursion
- ✅ Structs and enums
- ✅ Arrays (including push, get, pop)
- ✅ Closures with captured variables
- ✅ String creation and basic operations
- ✅ Pattern matching (simple cases)
- ✅ Loops and control flow
- ✅ Print with proper string formatting
- ✅ Inline IR instructions

## Known Issues

### 1. String Mutability (High Priority)
- **Problem**: Strings created from literals point to static memory, causing segfaults when mutated
- **Tests**: `interprets_simple_string_append`, `interprets_string_append`
- **Solution**: Ensure String.init always allocates heap memory, even for literals
- **Impact**: Critical for real-world usage

### 2. Missing Core Features (Medium Priority)

#### IO Operations
- The v1 interpreter has `interprets_io` test
- Need to implement IO instructions for reading/writing
- Required for interactive programs

#### Built-in Optional Type
- The v1 interpreter has `interprets_builtin_optional` test
- Need to ensure Optional works correctly with pattern matching
- Important for idiomatic Talk code

#### Division Operation
- The v1 interpreter has explicit `interprets_div` test
- Should verify division by zero handling
- Edge case coverage

## Compiler Limitations (Not Interpreter Issues)

These tests are ignored because the compiler doesn't support these features yet:
1. **Match guards**: `if` conditions in match arms
2. **Tuple destructuring**: `let (a, b) = tuple`
3. **Array destructuring**: `let [first, ...rest] = array`
4. **Struct pattern matching**: Matching on struct fields
5. **Multiple patterns**: `case A | B =>`

## Missing Optimizations

### 1. Memory Management
- Current arena allocator never frees memory
- No garbage collection or reference counting
- Memory usage grows unbounded in long-running programs

### 2. Performance
- No instruction caching or optimization
- Every operation allocates new memory
- No constant folding or dead code elimination

## Feature Parity Checklist

Features to verify/implement for full v1 parity:

- [ ] **Array operations**: Ensure all array methods work (v1 has `interprets_array_push_get`)
- [ ] **Special string cases**: v1 has `interprets_string_special_case` - need to understand what this tests
- [ ] **Return statements**: v1 has explicit `interprets_return` test
- [ ] **Complex recursion**: v1 has `interprets_fib` and `interprets_more_fib`
- [ ] **Function calls**: v1 has explicit `interprets_call` test
- [ ] **Binary operations**: v1 has `interprets_simple_binary_ops`

## Recommended Priority Order

1. **Fix string mutability** - This is causing actual test failures
2. **Add missing arithmetic tests** - Easy wins for completeness
3. **Implement IO operations** - Needed for real programs
4. **Verify Optional support** - Important for Talk idioms
5. **Add memory management** - Long-term sustainability

## Testing Strategy

1. **Port all v1 tests**: Systematically go through v1 tests and ensure v2 has equivalent coverage
2. **Add stress tests**: Large arrays, deep recursion, many allocations
3. **Error cases**: Division by zero, null pointer access, stack overflow
4. **Performance benchmarks**: Compare v1 vs v2 performance

## Implementation Notes

### String Mutability Fix
The issue is that string literals create String structs pointing to static memory. When String.append is called, it tries to modify this static memory. Solutions:
1. Make String.init always copy to heap (simple but less efficient)
2. Add copy-on-write semantics (more complex but efficient)
3. Track memory location type in String struct (moderate complexity)

### Memory Management
Consider implementing:
1. Reference counting for automatic cleanup
2. Generational garbage collector
3. Linear types to prevent use-after-free
4. Arena cleanup between function calls

## Success Criteria

The v2 interpreter will be considered feature-complete when:
1. All v1 interpreter tests pass (except those requiring compiler features)
2. No segfaults or memory corruption
3. Performance is within 2x of v1 interpreter
4. Can run the Talk compiler itself (self-hosting test)