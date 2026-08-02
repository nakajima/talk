# 0045 - Aggregate layout

Status: accepted; implemented 2026-08-01 across the compile pipeline
and both backends. MIR computes and publishes layout as replacing
structure — the interned layout table, per-instruction layout ids
(constructions and every field access carry their container's layout),
per-function locals tables, frame sites, and calling conventions. The C
backend consumes it end to end: native untagged structs for inline
aggregates, native direct-call signatures, reabstraction only at
genuine representation boundaries. The VM consumes it as its one value
representation: flat aggregates under published layouts, built by one
`AggNew` opcode and read by slot offset, in bytecode format 6 whose
every image ships its layout table. The MIR cleanups landed with it
(the escape analysis and locals table are MIR-owned; `c_escape.rs`,
`n_locals`, `MemTy::size`, and the builder's typing side maps are gone;
explicit-init receivers are declared `Blank` cells).

The VM slice also shipped 2026-08-01, as a single-representation
rewrite rather than a migration: the VM has exactly one aggregate value
(`Value::Agg` — a flat slot vector under a published layout id, nested
inline children spliced in place, a sum's tag at slot 0), one
construction opcode (`AggNew`, carrying a layout id and case tag — no
symbols on the wire; identity lives in the layout table), and
offset-addressed `Field`/`SetField`. The bytecode format is 6 with the
floor at 6: every image ships its layout table, and there is no legacy
decode path — the transition existed only transiently while the
bootstrap artifact regenerated. The read collapse (one tag-carrying
`Field` in MIR) and the `'heap` recursion rule (rule 2, judged by the
shared expandability oracle) shipped the same day.

Both closing slices shipped 2026-08-01. Init-receiver unwind is
initialization-aware: an abort through an initializer drops exactly the
fields assigned so far, in reverse order — the C++/Swift/Rust
partial-initialization rule in its zero-runtime-state variant (one
shared shadow ownership entry per receiver field; initialization state
must be path-uniform at joins, a diagnostic rather than a drop flag).
That fixed a latent trap (the old structural drop `Free`d the storage
field's unit placeholder) and made blankness unobservable, so the
placeholder machinery — `constants_fit`, the broken-contract demotions,
the tagged-blank carve-outs — is deleted. On that substrate, the C
backend's boxed aggregates store the native structs behind a
`TALK_NATIVE` box (box/unbox are copies; one boxed form per layout,
blank receivers included, as zeroed storage; sums and `InlineArray`
keep tagged boxes for their dynamic reads; rendering converts, and the
region scan walks generated per-layout member paths). That removed the
native/boxed conversion tax: `drops` went from 44ms to 26ms, below even
the pre-native-signature 36ms.

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

The indirection is *required* to be named in source: a recursive type
without it is a diagnostic, never a silent allocation. This matches the
language's grain — ownership transfer, borrows, and effects are already
explicit, and a hidden allocation at a recursive edge would be the odd
one out.

The marker is `'heap` (implemented 2026-08-01), not a new keyword:
`'heap` already means "this declaration's values live behind a
reference," heap values are value-like in use (matched, structurally
compared, deterministically dropped), and recursion is simply the case
where that indirection is not optional. Enums accept `'heap` for this —
at runtime a heap enum is exactly the boxed variant both backends
already build, so the declaration is pure published truth. The rule is
one-directional: recursive-and-not-`'heap` errors; `'heap` on a
non-recursive type remains an ordinary choice.

Precision is part of the rule: `[Node]` does not make `Node` recursive,
because array elements live behind `Storage`'s raw pointer. Recursion is
judged with per-declaration parameter *expandability* (does `T<…, X, …>`
place `X` inline?), a fixpoint over declarations implemented once —
`types::catalog::expandable_params`/`is_layout_recursive` — and consumed
by both the checker's diagnostic and the layout classifier, which must
agree exactly. That precision is what leaves the frontend's own AST
enums unannotated: their children arrive through arrays, which are
already indirect.

### 3. Width bounds boxing for the rest

An aggregate wider than a threshold is boxed even when finite, because
copying it by value costs more than an indirection. Swift's existential
container takes the same shape with a three-word inline buffer. The
threshold is a tuning parameter, not a semantic one: it may change without
changing what a program means.

The initial threshold is four words (32 bytes), a named constant consulted
only by MIR's layout classifier — typing never reads it, which is what
keeps it unobservable. It gets retuned against the parser workload once
inline layout is emitting; the 5.3 M-allocation measurement above is the
benchmark.

### 4. Layout is published structure, and locals carry types

MIR gains, per aggregate type: total width, per-field offsets, and the
inline/boxed classification, held in a program-level layout table alongside
the existing `struct_index`/`enum_index`. MIR locals gain types: `Function`
carries a locals table, so that a local holding an inline `Point` is two
words rather than one uniform slot.

This is the enabling half of the decision. Without typed locals a backend
cannot allocate storage of the right shape, and every layout fact MIR
published would be unusable.

It is also structure, not annotation. Nothing arrives as a side table over
untyped slots; the new facts replace the mechanisms that approximated them:

- the locals table absorbs `Function.n_locals` and the builder-internal
  `owned_tys` map, which types exactly the droppable locals and is
  discarded after drop emission (mir/mod.rs:2475);
- the layout table subsumes `MemTy::size`, today's only width arithmetic
  (mir/mod.rs:363), so buffer element stride and aggregate field offset
  come from one place;
- `GetField`, `TupleGet`, and `GetPayload` are a single positional read
  once layout defines what a position is, and collapse into one
  instruction;
- the C backend's escape pass moves into MIR's site classification — its
  own header already calls it analysis MIR should own (c_escape.rs:9).

The measure of "integral" is the diff: each mechanism replaced leaves the
tree in the same change that supersedes it.

### 5. Layout does not change ownership

An inlined aggregate containing a buffer still owns that buffer, and its
release is placed exactly where `mir/release.rs` places it now. Inlining
moves where bytes live; it does not move who owns what. ADR 0044's four
substrates and their lifecycle rules are unchanged — this ADR determines the
*shape* of a value within whichever substrate holds it.

### 6. Executed instances are concrete; `Ty::Param` gets a check-only layout

The original proposal left generics open, framing per-type layout as
"monomorphization-shaped, which ADR 0038's witness-passing architecture
deliberately avoids." That framing is stale: below the checker, MIR already
compiles function bodies per demanded instance. `demand` (mir/mod.rs:1785)
is a worklist keyed by the substitution pruned to the callee's scheme
parameters; call sites resolve their checker instantiation through the
enclosing instance's own substitution, so from a concrete entry every
executed instance is fully ground. Verified directly: a generic swap over
`Pair<T>` used at `Int` and `Float` compiles to two functions, called
directly, with no witness arguments. Witness arguments accompany only the
`Ty::Param`s remaining in a substitution (`witness_params`,
mir/mod.rs:1189), and rigid identity-substitution instances are demanded
only under check-all (mir/mod.rs:1347), where they prove every body
compiles and are never emitted or executed.

What ADR 0038 protects is unchanged by saying so: schemes stay canonical
and typechecking runs once. Per-instance compilation below the checker is
the existing status quo, not a new cost of this ADR.

So layout needs no runtime answer for `Ty::Param`. Executed construction
sites have concrete field types and classify as inline or boxed under rules
2 and 3; the rigid check instances get an opaque layout — no width, no
offsets, legal to construct and ownership-verify, rejected at emission.
Boxing is not a fallback for type parameters because type parameters never
reach a backend.

Two consequences of relying on this must be pinned by tests: polymorphic
recursion (a body demanding itself at a larger instantiation must reject
rather than diverge the worklist), and unbound enum payload parameters
(`Result.err(99)` with `T` free), which must have a pinned demanded
substitution and payload layout.

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
that unchanged. This is already a live problem: the escape analysis had to
read parameter summaries before register allocation for the same reason.

Resolution: the pass becomes layout-aware, merging only locals with
identical layout. That keeps the frame-size benefit — which the VM pays
per activation and the C stack guard has to bound — with the smallest
correct change. Deleting the pass outright stays on the table, but as a
measured decision once shaped frames exist, not a default.

### Both runtimes need a flat representation

`Value` was an enum whose aggregate variants held `Rc<Vec<Value>>`;
`TalkValue` is a uniform sixteen-byte tagged union with no per-type
shape. Each needs a representation for inline aggregates, and the
bytecode format needs field access by offset rather than by index into
a boxed vector.

The VM's answer (implemented 2026-08-01) is one flat aggregate:
`Value::Agg(layout, slots)`, where nested inline children splice into
the parent's slot vector — one allocation covers the whole inline tree,
which is what turns the allocation count from per-node into per-boxed-
node. Every access site is statically addressed because MIR publishes
the container's layout on the access instruction itself (`Field`,
`SetField`, and `GetElement` carry it; MIR knows the container type at
every emission site), so the interpreter executes slot offsets and
never consults a value's shape. The two deliberate exceptions are the
dynamic ones: `GetElement` strides by the published element layout
under a runtime index, and an existential `mut` requirement's writeback
tuple — whose payload element has no static width at the call site —
reads logically through the value's own published layout
(`FieldIndex`/`SetFieldIndex`, the abstraction boundary's read).
Constructions with unshaped layouts are a lowering error, except under
check-all, where rigid instances (any whose substitution retains type
parameters) verify and then ship as traps — rule 6's "rejected at
emission" made literal.

Identity questions dissolved into the table rather than being policed:
every construction interns its layout under its own declared symbol
(`InlineArray` keeps its symbol; a `'heap` enum's construction interns
its boxed sum shape while its embedding stays one slot), so the
broken-contract identity clause is gone and rendering reads the layout.
The classifier also normalizes ground associated-type projections
(`Optional<T.Item>` under `T := Concrete` interns the same layout as
`Optional<Int>`), and blank init receivers are flat too — a tagged slot
holds Unit until the initializer assigns it.

The C backend consumes the published layouts first (implemented
2026-08-01): an inline aggregate is a real untagged C struct — `int64_t`,
`double`, and pointer members under the platform ABI, the `repr(C)`
model — chosen over tagged slot arrays for interoperability, and because
rule 1 already says the runtime never inspects values. Locals classed to
an inline layout get struct storage; construction is member stores with
no allocation; field, payload, and tag reads are member reads. Emitting
this surfaced two facts the table must publish or the backend would have
to infer them, which rule 1 forbids: a per-field *representation* (a
one-slot field can be a scalar or a spliced one-slot aggregate — the
flattened slot kinds cannot say which, and reabstraction must rebuild the
aggregate), and the layout's source *nominal* (interning is therefore
identity-separated, so a `LayoutId` alone recovers the display symbol
when a value is re-boxed).

Where a native value crosses into a context that still expects the
uniform representation — a call argument, a return, a captured value, a
field of a boxed aggregate — it is reabstracted into a tagged box, the
Swift thunk model. When the escape analysis proves the value stays in
the frame, the box reuses a per-local frame buffer; otherwise it goes to
the arena, which is where the value would have been built before. Two
construction forms keep the uniform representation by demotion rather
than by guessing: sites whose declared identity disagrees with the
layout's nominal, and sites feeding a typed slot a constant it cannot
hold — MIR builds placeholder aggregates from `Unit` for memberwise
`init` to fill, and only a tagged slot can say "nothing here yet". Sums
whose payload elements are wider than one slot also stay uniform for
now: `GetPayload` does not carry the tag, so a static member read exists
only when every variant places element `j` at slot `j + 1`. The read-op
collapse in the format slice is the place to carry the tag and lift
this.

Direct calls pass structs natively (implemented 2026-08-01). MIR
publishes each function's calling convention — a `ParamRepr` per
parameter and the layout every return site agreed on — computed from the
checked types at build time, so caller and callee derive the same
signature from published facts and never from any one body. Rule 6 makes
this sound: every executed instance is monomorphic. A borrow of an
inline aggregate passes its pointee by value — aggregates have value
semantics (`SetField` copies; parameter mutation returns through the
writeback tuple), so the reference itself is never observable — and the
writeback tuple carries each evolved parameter as its value type, not
its borrow, which is what lets an `Array` round-trip through a
`push`-style loop without ever boxing. Zero-width fields (a Unit result
in a writeback tuple) occupy no struct member and reconstitute as Unit
at boundaries. The dispatch switch keeps the uniform convention and
converts per case, so indirect calls reach native-signature functions
unchanged. Because signatures are program-wide, the broken-contract set
is too: one contract-breaking construction site anywhere keeps that
layout uniform everywhere. An explicit initializer's receiver is no
longer such a site: it is a declared `Blank` instruction — a cell whose
every field is Unit until the init body assigns it, representable only
in the uniform tagged form — rather than a `Record` smuggling units into
typed slots. The initializer's `self` parameter therefore stays uniform,
while its *return* publishes the receiver's layout (the value is fully
assigned by then — definite assignment is the checker's guarantee), so
explicitly-initialized types like `String` are native end-to-end at
their call boundaries.

One subtlety is load-bearing: a value that arrives from outside the
frame — a native parameter, a native call result — must reabstract into
the arena, never a frame buffer, because nothing proved its box may die
with the frame; a `next`-style callee returning its evolved parameter
inside the writeback tuple would otherwise hand its caller a dangling
pointer.

These facts are MIR-published, not backend-derived (also implemented
2026-08-01): the escape analysis lives in `mir::escape`, and after
register allocation `shape_frames` stamps every `Function` with its
locals table — one `LocalInfo` per local carrying the layout class and
frame-locality, the table's length replacing `n_locals` — and its
frame-local construction sites. The C backend reads the table and only
filters for the layouts it can store; `c_escape.rs` and the emitter's
own derivations are deleted.

### The ABI and the frontend bridge move with it

ADR 0043's descriptor and `compiling::bridge` walked a value graph of
boxed records by index. The implemented resolution (2026-08-01) departs
from this ADR's original text in one deliberate way: the descriptor does
**not** carry offsets. The bytecode module already ships its layout
table, and duplicating offsets into the descriptor would create a second
source of representation truth. Instead the descriptor stays logical
(names, order, the four-constructor type language), and the runtime
exposes logical accessors — `RunOutcome::aggregate` (identity, case tag,
element count) and `RunOutcome::element` — that resolve through the
module's own published table. The bridge's validation and adaptation
walks are unchanged in structure and know nothing about representation.

No backwards compatibility is owed to the current formats, and none
survives: the bytecode is format 6 with the floor at 6. The one real
ordering constraint was the bootstrap cycle — the compiler that
regenerates the artifact must first load the old one to parse the
frontend's own sources — so the transitional decode paths existed
in-tree only between teaching the new format and the regeneration, and
were deleted the same day. The staleness gates and the fail-closed
version checks are what make a stale artifact loud rather than silent.

### Debug and display metadata

`ValueNames` maps symbols to type, field, and case names for rendering.
A flat aggregate has no per-field headers, so rendering is driven by
the published layout (implemented 2026-08-01): the value's layout id
recovers its identity and field structure from the table, and
`ValueNames` supplies the names. Nothing is recovered from slot
contents.

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

## Resolved questions

The original proposal left five questions open. All are now decided in
place (2026-07-31):

1. **Recursive marker** — required, not inferred; rule 2.
2. **Width threshold** — four words initially, consulted only by MIR's
   classifier, retuned by measurement; rule 3.
3. **Generics** — the executed path is already monomorphic; `Ty::Param`
   gets a check-only opaque layout; rule 6.
4. **regalloc** — layout-aware merging; the `reuse_locals` consequence.
5. **Migration order** — versions bump and regenerate together, with the
   bootstrap cycle as the only ordering constraint; the ABI consequence.

## Research and precedent

- Leroy, *Unboxed Objects and Polymorphic Typing*, POPL 1992: the canonical
  treatment of unboxed multi-word representations under polymorphism, and
  the coercion-based transformation that makes them typable. Rule 6 makes
  this the road not needed: coercions solve the problem of polymorphic code
  meeting unboxed values at runtime, and MIR's demand worklist already
  instantiates the executed path so that meeting never happens (the
  approach of Rust and C++, and of MLton's whole-program
  monomorphisation).
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
