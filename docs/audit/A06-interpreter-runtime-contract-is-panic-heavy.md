# A06: Interpreter runtime contract is panic-heavy

**Severity:** Medium  
**Area:** interpreter correctness model / runtime resilience  
**Primary files:** `src/ir/interpreter.rs`

## Summary

The interpreter currently relies on a large number of panic-based assumptions about IR validity, pointer correctness, value shape, and control-flow invariants. That can be acceptable for a strictly internal, trusted-IR debug executor. It is not acceptable if the interpreter is expected to serve as a resilient runtime for arbitrary user programs produced by the compiler.

The codebase has not fully chosen between those two models.

## Evidence

During audit, rough counts showed a high concentration of panic/todo/unimplemented sites in the interpreter relative to the rest of the codebase.

Examples include:

- arithmetic and comparison shape mismatches
- `Unreachable` execution
- branch condition type mismatches
- unsupported field access forms
- pointer-type assumptions
- memory indexing assumptions
- IO argument shape checks
- runtime representation mismatches for records, strings, and buffers

Representative locations:

- `src/ir/interpreter.rs:350` — unreachable path panics
- `src/ir/interpreter.rs:358` — non-bool branch condition panics
- `src/ir/interpreter.rs:498` — unsupported ref-taking is unimplemented
- `src/ir/interpreter.rs:572`, `:595`, `:619` — pointer assumptions in load/store/move
- `src/ir/interpreter.rs:654` — `Free` is unimplemented
- `src/ir/interpreter.rs:961` — current failing test path panics on out-of-bounds access

## Why this matters

A panic-heavy interpreter has these properties:

- small internal bugs become process aborts
- representation mismatches become crashes instead of runtime failures
- user-facing features can appear flaky when compiler invariants are incomplete
- test failures provide less structured information than explicit runtime errors

This is especially important because the surrounding compiler still has incomplete feature areas. When pipeline guarantees are imperfect, the runtime should ideally degrade gracefully rather than explode.

## Decision needed

The project should make the runtime contract explicit.

## Option A: Trusted IR debug executor

If this is the intent, document that:

- interpreter correctness assumes compiler-generated, fully validated IR
- panics indicate internal compiler/runtime bugs
- end-user robustness is not a goal for malformed IR or half-implemented features

This is a valid position, but it should be stated clearly.

## Option B: Real runtime surface

If this is the intent, many current panics should become structured runtime errors:

- invalid memory access
- bad value shape at runtime
- unsupported instruction form
- missing symbol metadata
- representation mismatches

## Recommended direction

Given the codebase already supports CLI execution and wasm execution, the interpreter appears to be more than a purely internal debugging tool. That argues for moving at least partway toward Option B.

A pragmatic compromise:

- keep `debug_assert!` or internal panics for impossible compiler invariants
- convert user-reachable memory/value/IO failures into interpreter error values
- ensure unsupported runtime instructions fail predictably

## Suggested implementation plan

1. Introduce an interpreter error type.
2. Convert the highest-risk panic sites first:
   - memory bounds
   - string/path extraction
   - unsupported instructions
   - invalid branch/value shapes caused by incomplete lowering
3. Return structured failures through CLI and wasm surfaces.
4. Reserve panics for genuine internal impossibilities.

## Acceptance criteria

- User programs cannot crash the interpreter process through ordinary runtime misuse or incomplete language support.
- Out-of-bounds and representation failures become reported interpreter errors.
- Unsupported runtime instructions have explicit failure behavior.
- The intended runtime contract is documented.

## Related issues

- [A02](./A02-interpreter-string-path-io-mismatch.md): a current correctness bug escalates to panic because runtime bounds and error handling are weak
- [A03](./A03-user-reachable-todo-and-unimplemented-paths.md): incomplete lowering/runtime support currently feeds panic-heavy execution paths
- [A05](./A05-interpreter-byte-conversion-overhead.md): a good time to harden and optimize the interpreter is during the same subsystem pass
