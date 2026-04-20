# A05: Interpreter byte conversion overhead

**Severity:** Medium-high  
**Area:** interpreter performance  
**Primary files:** `src/ir/interpreter.rs`

## Summary

The interpreter repeatedly allocates and copies `Vec<u8>` values in core memory operations. That is simple and readable, but it is likely one of the biggest avoidable sources of runtime overhead in the current executor.

The main hotspots are the generic value/byte conversion helpers:

- `value_to_bytes()`
- `bytes_to_value()`

## Evidence

Key functions:

- `src/ir/interpreter.rs:992` — `fn value_to_bytes(&mut self, ty: &IrTy, value: Value) -> Vec<u8>`
- `src/ir/interpreter.rs:1062` — `fn bytes_to_value(&self, ty: &IrTy, bytes: &[u8]) -> Value`

These helpers are used by interpreter instructions such as:

- `Load`
- `Store`
- `Move`
- record materialization / dematerialization

They also recurse for record fields and often allocate fresh vectors even for tiny primitive values.

## Why this matters

Interpreter performance is dominated by repeated small operations. In that environment, the following patterns are expensive:

- allocating a fresh `Vec<u8>` for primitive loads/stores
- serializing entire record values just to write memory
- deserializing whole record byte slices back into nested `Value`s
- copying through intermediate vectors instead of reading/writing slices directly

This overhead especially hurts:

- loops
- data-heavy code
- string and record manipulation
- core-library operations layered on top of memory primitives

## Current trade-off

The current implementation optimizes for implementation simplicity:

- one generic path for all value kinds
- easy-to-read recursion for records
- straightforward use in `Store` / `Move` / `Load`

That is a reasonable starting point. It becomes less reasonable once the interpreter is expected to be a serious execution target.

## Recommended improvements

## 1. Split primitive fast paths from generic paths

For primitive types like:

- `Int`
- `Float`
- `Bool`
- `RawPtr`
- `Byte`

use direct slice reads/writes instead of intermediate `Vec<u8>` allocation.

## 2. Add write-into-slice helpers

Instead of `value_to_bytes() -> Vec<u8>`, prefer APIs like:

- `write_value_into(&mut [u8], &IrTy, &Value)`
- `read_value_from(&[u8], &IrTy) -> Value`

That lets the caller own the destination buffer and eliminates many temporary allocations.

## 3. Avoid full record reserialization when possible

If a caller only needs to move or store a value already in memory-compatible layout, it may be possible to write fields directly into the destination slice.

## 4. Use stack buffers for fixed-size primitive cases

Many primitive sizes are known and tiny. A stack array can avoid heap traffic.

## 5. Re-enable and modernize benchmarks

The repository currently has benchmark remnants, but bench entries are disabled and the checked-in bench sources appear stale. Real measurements would help validate improvements.

## Acceptance criteria

- Primitive load/store paths do not allocate heap vectors.
- Record-heavy paths materially reduce allocation counts.
- Interpreter benchmarks exist again and cover representative workloads.
- Performance-sensitive changes are verified by benchmarks, not guesswork.

## Related issues

- [A04](./A04-lsp-full-workspace-rebuild-behavior.md): both are performance issues, though in different runtime contexts
- [A06](./A06-interpreter-runtime-contract-is-panic-heavy.md): interpreter hardening and interpreter optimization are best treated as one focused subsystem pass
- [A10](./A10-repo-hygiene-and-archaeology-debt.md): bench cleanup is a prerequisite for reliable measurement
