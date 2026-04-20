# A08: `CaptureIO::read_stdio` does not match real stdio semantics

**Severity:** Medium  
**Area:** test runtime / IO fidelity  
**Primary file:** `src/ir/io.rs`

## Summary

`CaptureIO::read_stdio()` reports the size of the queued stdin buffer before reading, not the number of bytes actually copied into the caller's buffer. That diverges from normal read semantics and can make tests pass or fail for the wrong reasons.

## Evidence

`src/ir/io.rs:385`

Current behavior:

- capture `let len = self.stdin.len();`
- iterate over the destination buffer and pop as many bytes as the destination can hold
- return `Ok(len)`

This means the function may return a value larger than the actual number of bytes written into `bytes`.

## Example

If:

- stdin queue contains 100 bytes
- caller provides an 8-byte buffer

The function currently:

- writes 8 bytes into the buffer
- returns `100`

Real `read()`-like behavior should return `8`.

## Why this matters

Tests using `CaptureIO` are supposed to approximate runtime behavior. If the test double reports impossible read counts, it can:

- hide buffering bugs
- break loops that trust the returned count
- create discrepancies between interpreter tests and actual runtime behavior
- make future stdin-based features harder to trust

## Recommended fix

Return the number of bytes actually copied.

Pseudo-behavior:

1. compute `to_read = min(bytes.len(), self.stdin.len())`
2. pop exactly `to_read` bytes
3. fill only that prefix of the destination slice
4. return `Ok(to_read)`

Also ensure unread bytes remain queued.

## Suggested tests

Add focused tests covering:

- queue shorter than buffer
- queue longer than buffer
- empty stdin queue
- multiple sequential reads

## Acceptance criteria

- `CaptureIO::read_stdio()` returns the number of bytes actually written into the destination buffer.
- Repeated reads drain stdin incrementally and predictably.
- Behavior matches the broad expectations of POSIX/std IO reads used elsewhere in the interpreter.

## Related issues

- [A06](./A06-interpreter-runtime-contract-is-panic-heavy.md): better test doubles help catch runtime mistakes before they become panic bugs
- [A02](./A02-interpreter-string-path-io-mismatch.md): another example where IO boundary assumptions currently drift from intended semantics
