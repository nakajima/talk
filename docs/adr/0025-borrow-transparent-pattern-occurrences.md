# 0025 - Pattern occurrences are borrow-transparent

Status: accepted (2026-07-10)

## Context

Talk has borrow types but no owned/borrowed pattern syntax. A programmer writes
the same pattern for an owned enum and a borrowed enum:

```talk
match value {
    .some(payload) -> payload,
    .none -> fallback
}
```

The checker already honored that rule when the entire match scrutinee was a
borrow. `check_match_arms_against` removed one outer `Borrow` before checking
all arms, and lowering separately remembered that every payload binder aliased
the borrowed scrutinee.

That root-only rule fails when a borrow appears below an aggregate:

```talk
func equals(lhs: Optional<T>, rhs: Optional<T>) -> Bool {
    match (lhs, rhs) {
        (.some(a), .some(b)) -> a == b,
        (.none, .none) -> true,
        _ -> false
    }
}
```

Borrow-by-default parameters make the tuple type
`(&Optional<T>, &Optional<T>)`. The tuple pattern introduces one pattern
occurrence per element, but the checker tried to unify each variant pattern's
owned `Optional` shape directly with `&Optional<T>`. The resulting type errors
also disconnected the payload types and made exhaustiveness lower the invalid
variant patterns as catch-alls, producing false unreachable-arm warnings.

Erasing every borrow deeply from the scrutinee type is not correct. In
`Optional<&T>`, the nominal application and its payload type must remain
`Optional<&T>` until the payload occurrence is examined. Binders must also keep
explicit borrow-typed payloads (`.some(x)` over `Optional<&T>` binds `x: &T`).
Pattern shape and ownership therefore need related but distinct facts.

## Decision

A pattern is checked as a tree of **pattern occurrences**. Borrowing is
transparent whenever a refutable pattern inspects the shape of its current
occurrence. Ownership is still tracked for the projection path to each binder
or wildcard.

### 1. Occurrence-level pattern view

At each tuple, record, variant, or literal pattern occurrence:

```text
pattern_view(&T) = T
pattern_view(&mut T) = T
pattern_view(T) = T otherwise
```

The view removes only borrows around the current occurrence. It does not walk
inside nominal arguments, tuple elements, record fields, or variant payloads.
Those children receive their own view if and when their sub-pattern inspects
them.

Irrefutable binders and wildcards do not need a shape view. An explicit borrow
at their occurrence remains in the binder type. This preserves
`Optional<&T>` payload typing while still allowing a constructor pattern to
inspect an `&Optional<T>` occurrence.

When an occurrence's head is unresolved, `PatternView` defers the choice until
the solver knows whether the occurrence is borrowed. The match root creates
one shared view for all arms; recursive aggregate projections create their own
views.

### 2. Exhaustiveness uses the same view

Coverage and reachability inspect the borrow-transparent type at every matrix
occurrence. Constructor universes, constructor applicability, and constructor
field types all use the current occurrence's view.

Coverage does not interpret a failed borrowed constructor pattern as a
catch-all. It reports reachability and missing cases from the same shapes the
type checker accepts.

### 3. Ownership remains projection-specific

Borrow transparency does not transfer ownership. Every lowering occurrence
carries two facts:

- the checker type visible to pattern shape compilation;
- whether its projection path crossed a borrow.

Projecting through a borrowed tuple, record, or variant keeps every child
borrowed. Projecting an explicitly borrowed child of an owned aggregate makes
only that child borrowed. Variant payload binders and wildcard payloads inherit
the occurrence ownership.

Only owned wildcard occurrences are dropped. Only owned binders receive
arm-scope drops. Borrowed binders are aliases and never release their owner's
storage.

### 4. Flow tracks binder ownership by pattern path

Flow walks the solved scrutinee type alongside each arm pattern and computes
the borrow permission for each binder projection. It no longer classifies all
binders from only the match root.

A binder whose path crosses a borrow:

- receives the scrutinee's provenance;
- is registered as a borrowed root at the projected permission;
- remains initialized without becoming an owner.

This supports mixed aggregates such as `(&Optional<String>, Optional<String>)`:
the first payload aliases its source while the second payload retains ordinary
owned drop behavior.

## Invariants

1. Pattern syntax never distinguishes owned from borrowed constructors.
2. A borrow is removed only at the occurrence whose shape a pattern inspects.
3. Explicit borrow-typed binder payloads keep their borrow type.
4. Type checking, exhaustiveness, lowering, and flow agree on occurrence
   boundaries.
5. Crossing a borrow changes ownership/provenance even when the binder's
   surface type is the viewed inner type.
6. Borrowed wildcard payloads are not dropped; owned wildcard payloads still
   are.
7. Mixed owned and borrowed aggregate elements are classified independently.

## Rejected alternatives

### Add borrowed pattern syntax

Rejected because ownership is not part of pattern selection in Talk. There is
no runtime constructor distinction to express, and requiring syntax would make
ordinary matches depend on the caller's access mode.

### Deeply erase borrows from the scrutinee type

Rejected because it changes nominal applications and payload types before
projection. `Optional<&T>` must not become `Optional<T>`.

### Rewrite tuple matches into nested matches

Rejected as a source workaround. It changes control-flow shape and leaves the
same compiler defect for records, deeper tuples, and generated code.

### Keep a root-level borrowed flag

Rejected because one aggregate can contain both owned and borrowed
occurrences. A root flag either drops aliases or leaks owned payloads.

## Validation

Regression coverage includes:

1. type checking and exhaustiveness for tuple elements that are borrowed enums;
2. deferred nested `PatternView` inference;
3. evaluator and VM parity for borrowed enum tuple matching;
4. repeated matching while the original owners remain usable;
5. allocation balance for borrowed payload aliases;
6. allocation balance for a mixed tuple whose borrowed payload aliases and
   whose owned wildcard payload drops;
7. existing top-level borrowed enum and `Optional<&T>` payload behavior.

## Consequences

- Pattern semantics become uniform across match roots and nested aggregate
  projections.
- Exhaustiveness no longer emits cascading unreachable warnings for valid
  borrowed constructor patterns.
- Lowering carries ownership per decision-tree occurrence instead of one bit
  for the whole match.
- Flow's binder seeding is more precise for mixed aggregates.
- The implementation adds no syntax and no runtime representation.

## Relationship to earlier ADRs

- **ADR 0018:** borrow-by-default parameters can be matched through aggregate
  expressions without exposing their implicit borrow mode in patterns.
- **ADR 0019:** this decision defines the semantic ownership facts that match
  payload operations must eventually carry explicitly in `CheckedMir`. The
  current decision-tree lowerer records them per occurrence until that cutover.
- **ADR 0021:** preserves `Optional<&T>` payload binder types and provenance
  while extending the same behavior to borrows nested below tuples and
  records.
