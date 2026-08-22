# 0070 - Trapping integer arithmetic with explicit checked and unchecked APIs

Status: accepted, implemented

## Context

TalkTalk's signed 64-bit `Int` operations previously wrapped modulo `2^64`.
That made overflow deterministic across the VM and C targets, but it also made
ordinary application errors look like plausible values. In particular,
`255!` evaluated to zero after accumulating enough factors of two modulo
`2^64`.

There are three distinct caller intentions:

1. ordinary arithmetic, where an out-of-range result is a program failure;
2. validation, where overflow should be represented as data; and
3. modular arithmetic, where retaining the low 64 bits is intentional.

One silently wrapping operator cannot express all three safely.

## Decision

`Int` remains signed 64-bit, but ordinary arithmetic traps on overflow:

- add, subtract, multiply, and negate trap when the mathematical result is
  outside the `Int` range;
- division traps on zero and on `Int::MIN / -1`;
- shifts and bitwise operations keep their existing bit-level semantics.

Core exposes two explicit method families:

- `checked_add`, `checked_sub`, `checked_mul`, `checked_div`, and `checked_neg`
  return `Int?`, using `.none` for overflow or division by zero;
- `unchecked_add`, `unchecked_sub`, `unchecked_mul`, `unchecked_div`, and
  `unchecked_neg` implement arithmetic modulo `2^64`. Unchecked division maps
  `Int::MIN / -1` to `Int::MIN`, but still traps on zero because division by
  zero has no modular result.

The VM and native runtime perform the same overflow checks and report the same
operation-specific trap category. The bytecode format advances to version 11
because existing arithmetic opcode tags acquire new observable semantics; the
compatibility floor advances with it. Constant folding uses Rust's `checked_*`
operations and leaves an overflowing instruction executable so optimization
cannot erase its trap. Dead-code elimination likewise retains unused integer
arithmetic that may trap.

The unchecked Core methods are ordinary source implementations over bitwise
operations and shifts. This keeps the target scalar instruction set singular:
backend arithmetic always has the safe default semantics, while wrapping is an
explicit library operation.

## Consequences

- Existing programs that relied on implicit wraparound must call an
  `unchecked_*` method.
- Overflow is fail-fast by default without adding an effect to every arithmetic
  expression.
- Callers that need recoverable validation avoid a panic handler and branch on
  `Optional` instead.
- Checked and unchecked methods are available on every target through Core.
- Existing format-10 images must be rebuilt rather than executed with changed
  arithmetic semantics.
- Integer arithmetic is now potentially trapping even when its result is
  unused, so optimizers must preserve it unless they prove the operation is in
  range.

## Validation

1. Core tests cover every boundary and all three modes.
2. VM tests require operation-specific overflow traps and exact unchecked
   wraparound values.
3. C differential tests cover checked and unchecked results, and a native
   overflow test requires a nonzero exit with the overflow message.
4. Constant-folding and dead-code tests retain overflowing operations.

## Relationship to existing decisions

This decision supersedes the wrapping `Int` arithmetic paragraph in ADR 0032.
It does not change literal range checking, Float arithmetic, Byte bitwise
operations, static-value arithmetic, or shift masking.
