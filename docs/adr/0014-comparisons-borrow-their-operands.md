# 0014 — Comparisons borrow their operands

Status: implemented (2026-07-04)

(0013 is reserved by the sequential-scoping ADR, in flight on the
sequential-scoping worktree.)

## Context

`Equatable` and `Comparable` took their right-hand side by value:

```talk
func equals(rhs: RHS) -> Bool
```

Comparison is a read, but a by-value `rhs` claims ownership. Two
problems fall out:

- **Borrowed operands need an escape hatch.** Iterators yield
  `&Element`, so `xs.iter().index(needle)` compares borrows. Feeding a
  borrow to a by-value parameter leans on the copy-out-of-borrow
  coercions (Copy erasure, CheapClone retain) — which cover scalars and
  buffers but not plain structs, where the call is only accepted via the
  caller's `Equatable<Element>` given plus runtime borrow erasure.
- **The by-value witness is an ownership leak.** A conforming
  `equals(rhs: Pt)` receives an owned value the borrow checker believes
  was copied out of a borrow; a witness that *stores* its rhs would
  smuggle an affine value out of a borrow. Nothing in core does this,
  but the signature invites it.

## Decision

Read-only comparison requirements take their operand by shared borrow:

```talk
public protocol Equatable {
	associated RHS
	func equals(rhs: &RHS) -> Bool
	func notEquals(rhs: &RHS) -> Bool { ... }
}

public protocol Comparable: Equatable {
	associated RHS
	func gt(rhs: &RHS) -> Bool
	// gte / lt / lte defaults forward the borrow
}
```

Arithmetic (`Add`, `Subtract`, `Multiply`, `Divide`) stays by value:
those operations consume operands to produce a new value, and their
`Ret` makes the ownership transfer part of the contract.

Precedent, per decision:

- rhs by borrow: Rust's `PartialEq` is `fn eq(&self, other: &Rhs)`
  precisely so references compare through blanket impls
  (https://doc.rust-lang.org/std/cmp/trait.PartialEq.html). Swift, once
  it grew ownership, moved noncopyable comparison entry points to
  `borrowing` parameters (SE-0437,
  https://github.com/swiftlang/swift-evolution/blob/main/proposals/0437-noncopyable-stdlib-primitives.md;
  conventions from SE-0377,
  https://github.com/swiftlang/swift-evolution/blob/main/proposals/0377-parameter-ownership-modifiers.md).
- arithmetic by value: Rust's `Add::add(self, rhs: Rhs) -> Output`
  consumes both operands for the same reason talk's does
  (https://doc.rust-lang.org/std/ops/trait.Add.html).
- keeping the `RHS` associated type (rather than hard-coding `&Self`):
  matches Rust's `Rhs = Self` default type parameter; nothing in-tree
  binds it heterogeneously today, but the door stays open at zero cost.

## Consequences

- Witnesses for non-Copy types must annotate the borrow
  (`func equals(rhs: &String)`); Copy-graded types may keep by-value
  annotations because `&T ~ T` erasure unifies them either way.
- Runtime is unchanged: borrows erase in `map_ty`, so `@_ir` witness
  bodies and dispatch are byte-identical.
- `needle == candidate` over borrowed elements no longer round-trips
  through copy-out coercions or the given-equality escape hatch — the
  borrow flows straight through, for any grade.
