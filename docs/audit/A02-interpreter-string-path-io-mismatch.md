# A02: Interpreter string/path I/O mismatch

**Severity:** High  
**Area:** interpreter / string representation / file I/O  
**Primary files:** `src/ir/lowerer.rs`, `src/ir/interpreter.rs`, `core/File.tlk`  
**Visible symptom:** failing tests in `cargo test --workspace`

## Summary

The interpreter currently mixes two incompatible conventions:

- Talk `String` values are length-based: `(base, length, capacity)`
- `Interpreter::get_bytes_from_value()` treats a `RawPtr` as a **null-terminated** byte string

That mismatch causes out-of-bounds reads and is already visible as failing tests.

## Evidence

### Lowered string literals are not null-terminated

`src/ir/lowerer.rs:1909`

`lower_string()` writes the unescaped bytes of the literal directly into static memory and stores:

- base pointer
- byte length
- capacity

No trailing `0` byte is appended.

### Interpreter raw-pointer byte extraction expects C-string semantics

`src/ir/interpreter.rs:951`

`get_bytes_from_value()` handles `Value::RawPtr(ptr)` by walking memory until it finds a zero byte.

That is valid only if the pointed-to memory is guaranteed to be null-terminated.

### Tests already fail

`cargo test --workspace` reported:

- `ir::interpreter::tests::interprets_io_open_and_close`
- `ir::interpreter::tests::interprets_io_open_write_read`

Both panic at `src/ir/interpreter.rs:961` with an out-of-bounds access.

### Core API surfaces the mismatch

`core/File.tlk` passes `RawPtr` paths into `_io_open()`:

- `File.open_read(path: RawPtr)`
- `File.open_write(path: RawPtr)`
- `File.open_append(path: RawPtr)`

The test path uses `"test.txt".base`, which is a pointer into a length-based `String` value, not a null-terminated C string.

## Root cause

There are effectively two models in play:

### Model A: Talk-native string

- owns or references bytes
- carries explicit length
- can contain interior zero bytes
- does not require a trailing terminator

### Model B: Raw pointer path buffer

- only a base address is known
- caller and callee assume bytes continue until `0`

The interpreter crosses from A to B without an explicit conversion.

## Failure modes

1. **Out-of-bounds read**
   - pointer walks off the end of static memory looking for `0`

2. **Adjacent-static-data bleed**
   - path bytes may accidentally include later static-memory contents until a zero happens to appear

3. **Non-deterministic behavior as layout changes**
   - unrelated string or static-memory changes can alter file-path behavior

4. **Interior-zero truncation**
   - even if bounds were safe, embedded zero bytes would truncate paths unexpectedly

## Recommended fix

Pick one representation boundary and enforce it everywhere.

## Preferred approach

Make file/path operations length-aware.

Examples:

- accept `String` instead of `RawPtr`
- or accept `(RawPtr, Int)` as `(ptr, len)`

That aligns with the language's existing `String` model.

## Alternative approach

If raw-pointer path ops are intentionally C-like, introduce an explicit conversion path that allocates or materializes a null-terminated buffer. Do **not** reinterpret a normal Talk string base pointer as a C string implicitly.

## Minimum short-term fix

Even before the API is redesigned:

- stop unbounded scanning past static memory or heap bounds
- fail with a structured runtime error if no terminator is found inside the accessible allocation

That will at least turn memory corruption/panic into a predictable failure.

## Suggested implementation path

1. Decide whether `_io_open` is Talk-string-based or C-string-based.
2. Update the core API to match that decision.
3. Update lowering and/or interpreter helpers accordingly.
4. Add tests covering:
   - plain string literal paths
   - heap-allocated strings used as paths
   - strings with embedded zero bytes
   - missing-terminator failure behavior if C-string mode remains

## Acceptance criteria

- `cargo test --workspace` becomes green again.
- `interprets_io_open_and_close` passes.
- `interprets_io_open_write_read` passes.
- No raw-pointer path read can run beyond the bounds of static memory or heap memory.
- The path ABI is documented and consistent across core, lowering, and interpreter.

## Related issues

- [A06](./A06-interpreter-runtime-contract-is-panic-heavy.md): the current bug escalates to a panic because the interpreter lacks defensive runtime error handling
- [A05](./A05-interpreter-byte-conversion-overhead.md): both issues touch the interpreter's value/byte boundary
