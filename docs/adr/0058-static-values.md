# ADR 0058: Source-visible static values

Status: implemented

## Context

String literal bytes already live in immutable module storage, but every
literal evaluation rebuilt the core `String` aggregate over those bytes. The
source type also hid the useful distinction between an ordinary owned value
and a value whose complete storage has program lifetime.

A string-only `StaticString` would solve the immediate representation problem
but duplicate the same concept for future immutable arrays, tables, and
structural constants.

## Decision

Talk exposes the generic type `Static<Value>`. A `Static<T>` proves that its
reachable storage is immutable and has program lifetime. Its constructor is
compiler-owned; ordinary source code cannot promote a runtime value into
static storage.

String literals support two contextual types:

- An unconstrained literal defaults to `String`, preserving existing inference
  for mutable bindings, arrays, generic calls, and operator chains.
- A literal checked against `Static<String>` has that type.

This follows Swift's source-compatibility choice while still allowing APIs to
state that they retain only static data.

`Static<String>` implements the read-only string surface and converts through
`Into<String>` and `Into<Substring>`. Conversion shares the immutable static
bytes; it does not copy them. Operations that produce new text, including
concatenation, return an ordinary `String`.

`Static<T>` transparently exposes stored fields of `T` for shared reads.
Methods and protocol requirements do not automatically forward from `T`:
`Static<T>` must declare the read-only operations it supports. This prevents a
mutating or consuming operation on `T` from becoming available accidentally.

## Representation

`Static<T>` is representation-transparent. The compiler emits the underlying
value's slots and uses the static wrapper only for typing and member selection.
A string literal therefore remains the flat three-slot String shape:

```text
static byte pointer, byte count, capacity
```

The bytecode backend lowers a literal to `StringLit`. A machine interns the
complete aggregate by `(static offset, length, layout)` and each execution
clones the cached `Rc`; it does not execute aggregate constructors.

The C and LLVM backends emit one descriptor per distinct literal. C caches a
native-layout value and LLVM caches its tagged uniform representation. These
descriptors have process lifetime and survive native library arena cleanup.
Static byte retain and release operations remain no-ops.

## Static eligibility

The generic type establishes the language model, but this change only gives
the compiler a constructor for string literals. Future static declarations or
constant evaluation must admit `Static<T>` only when `T` is deeply immutable
and statically representable. Values with destructors, linear resources,
mutable references, runtime heap ownership, or captured dynamic state are not
eligible.

## Consequences

- APIs can accept or return `Static<String>` without introducing a nominal
  string-literal type.
- Existing unconstrained string-literal inference remains `String`.
- Literal evaluation performs no aggregate allocation after a descriptor's
  first use.
- The model can later cover static arrays and structural constants without a
  new lifetime-specific nominal for each value family.
- Bytecode format version 8 adds the `StringLit` opcode while retaining version
  7 decoding because the module section layout is unchanged.
