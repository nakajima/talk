# 0045 - Aggregate layout

Status: proposed

## Context

ADR 0044 rule 1 already assigns this decision:

> Typing publishes checked facts... MIR chooses representation, layout, and
> lifetime. The runtime executes explicit operations; it does not inspect
> Talk types, scan source, or infer ownership from liveness or display
> names.

MIR does not currently exercise the layout half of that authority. It emits
`Record { dest, struct_symbol, args }`, `Tuple`, and `Variant` with no width,
no field offsets, and no indication of whether the value is finite. Locals
are untyped `u16` slots. A backend receiving that has one representation
available to it — a uniformly shaped, separately allocated cell — because
some aggregates are recursive and a uniform choice must accommodate the
worst case.

Both backends have made that choice independently and identically. The VM
holds `Value::Record(Symbol, Rc<Vec<Value>>)`; the C backend holds a
`TalkAgg` in an arena. A `Point { x: Int, y: Int }` is two machine words of
data and costs a separate allocation plus a reference count in either.

### What that costs, measured

Parsing one 193 KB source (`stdlib/syntax/Parser.tlk`) through the
self-hosted frontend:

| | |
| --- | ---: |
| aggregate allocations | 5,312,492 |
| per source byte | ~27 |
| bytes handed out | 254.5 MB |
| live at peak, with the VM's `Rc` reclaiming | ~96 MB |
| managed buffers, by contrast | 5.4 MB total |

Buffers — the substrate MIR *does* track, with explicit `Alloc`/`Free` — are
two percent of the traffic. Aggregates, which MIR does not track, are the
rest.

The cost is diffuse rather than hot. Across 3,323 construction sites the
largest single one accounts for 8.2% and the top fourteen for 48%. There is
no hotspot because the cost is uniform: it is one allocation per aggregate
value, everywhere.

Two further measurements bound what can be recovered without changing the
layout decision:

- **Escape analysis reaches 5%.** The C backend's frame-allocation pass
  (`src/backend/c_escape.rs`) proves non-escape at 78 of 3,323 sites, 291,866
  of 5.6 M constructions. It can choose where a box lives; it cannot decide
  that there is no box. In a parser most values genuinely escape — into
  block parameters, into calls, into the returned tree.
- **The gap shows up directly in codegen.** `bench/arith.tlk`, which
  allocates nothing, runs 465× the VM. `bench/fields.tlk`, identical but for
  constructing two two-field records per iteration, runs 27× — and reached
  27× only after frame allocation moved it from 12×. The order of magnitude
  between them is boxing.

### Why this is a MIR decision and not a backend one

Every mitigation available to a backend accepts the allocation and makes it
cheaper: reference counting reclaims sooner, an arena reset bounds growth
across calls, copy-on-write copies less often. None removes the allocation,
and each has to be built twice, once per target, with the two
implementations obliged to agree forever.

The decision that generates every instance is upstream of both: MIR never
says how wide an aggregate is, so no backend can store one inline.

## Decision

MIR chooses a layout for every aggregate value and publishes it. A backend
reads the layout; it does not infer one.

### 1. Two layouts

- **Inline.** The aggregate's fields are stored contiguously in place: in a
  frame slot, in an enclosing aggregate's field, in an array element, in a
  register pair. No allocation, no indirection, no identity.
- **Boxed.** The aggregate is one allocation and the value is a reference to
  it. This is today's uniform behaviour, retained for the cases that need
  it.

Inline is the default. Boxed is a consequence of a rule below, never a
default and never a fallback for "unknown".

### 2. Recursion forces boxing, and is the only thing that does so silently

A type whose layout contains itself has no finite width. Such a type is
boxed at the recursive edge. The cycle is detected on the nominal type
graph, so the decision is a property of the declaration, not of a site.

Following Swift's `indirect`, the boxed edge should be *nameable* in source
so a programmer can place it deliberately rather than discover it, and so a
type that is accidentally recursive is a diagnostic rather than a silent
allocation. Whether the marker is required or merely permitted is left open
below.

### 3. Width bounds boxing for the rest

An aggregate wider than a threshold is boxed even when finite, because
copying it by value costs more than an indirection. Swift's existential
container takes the same shape with a three-word inline buffer. The
threshold is a tuning parameter, not a semantic one: it may change without
changing what a program means.

### 4. Layout is a published fact, and locals carry types

MIR gains, per aggregate type: total width, per-field offsets, and the
inline/boxed classification. MIR locals gain types, so that a local holding
an inline `Point` is two words rather than one uniform slot.

This is the enabling half of the decision. Without typed locals a backend
cannot allocate storage of the right shape, and every layout fact MIR
published would be unusable.

### 5. Layout does not change ownership

An inlined aggregate containing a buffer still owns that buffer, and its
release is placed exactly where `mir/release.rs` places it now. Inlining
moves where bytes live; it does not move who owns what. ADR 0044's four
substrates and their lifecycle rules are unchanged — this ADR determines the
*shape* of a value within whichever substrate holds it.

## Consequences

### Both targets benefit

The 5.3 M allocations are paid by the VM as `Rc` allocation and drop pairs
and by the C backend as arena traffic. Removing them at the source improves
the interpreter — which every developer runs today — as much as the
ahead-of-time path.

### `regalloc::reuse_locals` conflicts with typed locals

The pass renumbers locals onto the smallest set whose live ranges do not
overlap, merging slots across types. In the C backend's emitted `fields.c`,
slot `l[5]` holds a `Point` and later an `Int`. Typed locals cannot survive
that unchanged. The pass must either become type-aware, merging only within
a type, or move behind the layout decision. This is already a live problem:
the escape analysis had to read parameter summaries before register
allocation for the same reason.

### Both runtimes need a flat representation

`Value` is an enum whose aggregate variants hold `Rc<Vec<Value>>`; it has no
inline-product variant. `TalkValue` is a uniform sixteen-byte tagged union
with no per-type shape. Each needs a representation for inline aggregates,
and the bytecode format needs field access by offset rather than by index
into a boxed vector.

### The ABI and the frontend bridge move with it

ADR 0043's descriptor and `compiling::bridge` walk a value graph of boxed
records. A layout change is an ABI change: the descriptor must carry
offsets, and the checked-in frontend artifact must be regenerated. This is
mechanical but not small, and the staleness gates make it visible rather
than silent.

### Debug and display metadata

`ValueNames` maps symbols to type, field, and case names for rendering. An
inline aggregate has no header carrying its symbol, so rendering must be
driven by static type information at the point of the value rather than
recovered from the value itself.

## Alternatives considered

### Reference counting the aggregate cells

Rejected as the primary answer, retained as a possible complement. Value
aggregates are acyclic by construction, so counting is complete for them —
no cycle collector is implied. It would take the C backend's 254 MB to about
96 MB on the measured parse, matching the VM, and costs a count touch per
copy.

But it reclaims allocations rather than preventing them, leaves ~96 MB live
for a 193 KB input, must be implemented once per target, and does nothing
for the `arith`-versus-`fields` codegen gap, which is about indirection and
not about lifetime.

### Resetting the arena per call

Rejected as sufficient, required regardless. Without it the C backend's
memory is unbounded across calls, which is disqualifying for a compiler that
parses file after file. With it, peak is still 249 MB for one 193 KB parse
and scales linearly with input. It bounds a symptom.

### Extending the escape analysis

Rejected on measurement. It reaches 5% of construction sites in the
frontend, and the values it cannot prove non-escaping are escaping for real
reasons. Improving the analysis — for instance admitting flow through block
parameters — raises that number without changing that an escaping aggregate
is still separately allocated.

### A faster allocator

Rejected. The arena is already a bump pointer; the VM's `Rc` is already
cheap per operation. Five million of anything is the problem, not the cost
of each.

### Leaving layout to each backend

Rejected. It is the status quo, it has produced two identical uniform-boxing
decisions made independently, and ADR 0044 already assigns the decision to
MIR. It also makes layout unavailable to the checker and to the ABI, both of
which need to agree with it.

## Open questions

These are deliberately unresolved; this ADR states the decision, not the
design.

1. **Is the recursive marker required or inferred?** Requiring it (Swift's
   `indirect`) makes allocation visible in source and turns accidental
   recursion into a diagnostic. Inferring it keeps the language smaller. The
   two differ in whether a programmer can be surprised by an allocation.
2. **What is the width threshold, and is it observable?** It must not change
   program meaning, which constrains where it can be consulted.
3. **How do generics interact?** A `Box<T>` inlined for `T = Int` and boxed
   for a large `T` is monomorphization-shaped, which ADR 0038's
   witness-passing architecture deliberately avoids. Uniform representation
   for type parameters is the conservative answer and costs inlining exactly
   where generics are used.
4. **Does `regalloc` become type-aware or move?** Affects frame sizes, which
   the C backend's stack guard already has to bound.
5. **What is the migration order?** The frontend artifact, the ABI
   descriptor, and the bridge are coupled to the current shape, and the
   bootstrap cycle means the frontend must keep parsing throughout.

## Research and precedent

- Leroy, *Unboxed Objects and Polymorphic Typing*, POPL 1992: the canonical
  treatment of unboxed multi-word representations under polymorphism, and
  the coercion-based transformation that makes them typable. The direct
  precedent for question 3 — it introduces coercions precisely where a
  polymorphic boundary meets an unboxed representation.
- Peyton Jones and Launchbury, *Unboxed Values as First Class Citizens in a
  Non-Strict Functional Language*, FPCA 1991: distinguishing boxed from
  unboxed in the intermediate language rather than in the code generator,
  which is the structural point of this ADR — the decision belongs in MIR,
  not in each backend's emitter.
- Shao and Appel, *A Type-Based Compiler for Standard ML*, PLDI 1995, and
  Tarditi et al., *TIL: A Type-Directed Optimizing Compiler for ML*, PLDI
  1996: carrying types through the intermediate language specifically so
  representation decisions can be made from them. The precedent for
  requirement 4, typed MIR locals.
- Swift's `indirect` enums and its existential container's three-word inline
  buffer: a shipping language that boxes exactly at recursive edges and above
  a width threshold, with the recursive case marked in source. The precedent
  for rules 2 and 3.
- Racordon et al., *Implementation Strategies for Mutable Value Semantics*,
  JOT 2022, as cited by ADR 0044: value aggregates as values rather than as
  objects with identity, which is what makes an inline layout admissible at
  all.
- Choi et al., *Escape Analysis for Java*, OOPSLA 1999, as cited by ADR 0044:
  escape analysis chooses a value's *substrate*. This ADR chooses its
  *shape*. The measurement above is the evidence that the first does not
  subsume the second.
