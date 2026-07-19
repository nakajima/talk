# 0021 - First-class iteration with access-marked sources

Status: implemented (revised 2026-07-08; status updated 2026-07-11 —
`for` is typed first-class over the resolved AST's `StmtKind::For`, its
`ForPlan` is consumed by `elaborate_for` in
`src/compiling/typed_program/build.rs`, and no `for` form survives into
the typed tree, exactly as "Type checker product" specifies)

## Context

Iteration is currently implemented by an early syntactic rewrite. During
`resolve_names()`, `src/desugar/lower_for_loops.rs` rewrites:

```talk
for pattern in iterable { body }
```

into ordinary source-shaped declarations, a `loop`, `.iter()`, `.next()`, and a
`match` on `Optional`, before name resolution runs. Every later phase must
rediscover source lifetime, iterator lifetime, element ownership, borrow
provenance, and drop order from synthetic ordinary expressions — and each phase
gets a different piece subtly wrong. The failures surface as ownership errors,
borrow errors, leaks, double drops, and invalid pointer reads (the loop binder
double-free class tracked by ADR 0017 is one instance).

Two structural facts generate the whole bug class:

1. **`for` is erased before the `TypedProgram`/`CheckedMir` seam** (ADR 0019),
   so no checked product records that iteration happened.
2. **Core insists array iteration yields borrowed elements, but the compiler
   cannot express that.** `IndexIterator` stores `inner: &T` and
   `Array._index_iterable_get` returns `Optional<&Element>` — legal only
   because `check_borrow_storage` exempts core wholesale
   (`src/flow/loans.rs`). The loop binder aliases a borrow but is typed owned,
   producing per-iteration drops of storage the source still owns.

Two prior attempts inform this revision:

- A first-class-`for` scratch branch kept `StmtKind::For` through typing and
  published a `ForPlan`, but its MIR lowering rebuilt the same synthetic
  typed-AST expressions and fed them back through ordinary expression
  lowering. The desugar moved later; flow and lowering saw the identical
  shapes; nothing was deleted. **Lowering `for` by synthesizing AST is the
  specific mistake this ADR forbids.**
- The same branch showed the true prerequisite: Talk has borrow *types* but no
  place/access model in the call checker. Method calls are checked as
  "infer receiver type, unify with self parameter". A `mut func next()` call
  is really an *exclusive access to the iterator place*, and until the checker
  can say that, a first-class `for` still fails at `.next()`. This also breaks
  ordinary non-loop code: `self.inner.next()` inside a `mut func` must be
  legal (projection through an exclusive root), while the same call through a
  `let inner: &Inner` field must be rejected (no shared→exclusive upgrade).

An earlier draft of this ADR proposed a single cutover branch for all of it.
That failed in practice. The dependency it feared — first-class `for` without
access-aware calls fails at `next()` — is an *ordering* constraint, not an
argument for a cutover: the access model lands first, then iteration builds on
it, and the suite stays green after every stage.

## Decision

Iteration becomes a first-class checked construct with three source-access
modes, spelled with the existing ADR 0018 call-site markers on the iterable
expression:

```talk
for foo in foos { ... }          // shared: does not move or mutate foos
for foo in mut foos { ... }      // exclusive: foos must be a mutable place
for foo in consume foos { ... }  // consuming: foos is dead after the loop
```

The iterable position is checked exactly like an argument position: the marker
is the existing `ArgMode` grammar, and the required source access is the same
`AccessKind` the call checker uses for receivers and arguments. The binder
stays a plain pattern; its type is exactly the selected iterator's `Element`
(`&T` for shared array iteration, `&mut T` for exclusive, owned `T` for
consuming, owned for generators/adapters that produce values).

Supporting this requires, in order:

1. an **access-aware call checker**: receivers and arguments are checked as
   accesses (shared / exclusive / consume) against places or values, not as
   plain type unifications;
2. a **general borrow-containing struct rule** replacing the core-only
   exemption, so `IndexIterator` stores its source borrow legally and carries
   provenance like any other borrow-containing value;
3. **first-class `For`**: parsed, resolved, and typed as one construct; the
   typed-tree build then elaborates it into ordinary typed nodes, so every
   later pass sees real code (see "Type checker product").

### Prior art

- **Rust** desugars `for x in it` to `IntoIterator::into_iter` + `next()` in
  the compiler (not pre-resolution), and selects among three iterators by the
  iterable expression: `v` consumes, `&v`/`.iter()` yields `&T`,
  `&mut v`/`.iter_mut()` yields `&mut T`
  (<https://doc.rust-lang.org/std/iter/trait.IntoIterator.html>,
  <https://doc.rust-lang.org/std/iter/>). Talk's `mut foos` / `consume foos`
  markers are the same selection with Talk's marker words instead of
  reference syntax.
- **Hylo** attaches its parameter conventions (`let`/`inout`/`sink`) to
  bindings and parameters uniformly; ownership modes are part of the
  declaration vocabulary, not per-construct special cases
  (<https://docs.hylo-lang.org/language-tour/functions-and-methods>).
- **Swift** was considered and rejected: its `IteratorProtocol.next()` yields
  owned elements over CoW snapshots
  (<https://developer.apple.com/documentation/swift/iteratorprotocol>), which
  would delete the borrow machinery entirely but pays a retain/release per
  non-scalar element and cannot express in-place mutable iteration. Talk
  keeps borrowed elements.

## Core concepts

### Place

A place is an addressable program location. V1 places:

```rust
Place::Local(Symbol)
Place::Field(Box<Place>, FieldSymbolOrLabel)
Place::Deref(Box<Place>) // only when the type grants the needed permission
```

Non-place expressions are values: a value can be read or consumed, but not
exclusively borrowed (v1 does not materialize mutable temporaries).

### Access

The call checker asks for an access, not only a type equality:

- **Shared** accepts a place or value, never moves, creates shared-borrow
  provenance when the result depends on it. Default for ordinary parameters
  and plain receivers under ADR 0018.
- **Exclusive** requires a mutable place; creates an exclusive loan for the
  duration required by the call/result; permits projection through an
  exclusive root (`self.inner` in a `mut func`); rejects projection through
  shared borrowed fields.
- **Consume** moves an owned value/place when legal; rejects borrowed values
  unless an explicit `copy` is requested and the type is copyable.

A method's receiver mode selects the access its receiver expression must
satisfy (`func` → shared, `mut func` → exclusive, `consuming func` →
consume). The checker publishes the resolved access facts (a `CallPlan`, or
equivalent side tables); lowering never reconstructs access from syntax.

### Borrow-containing structs

A struct that stores borrows — declared `&` fields, or generic payloads
instantiated at borrow types (`Optional<&Element>`) — is a borrow-containing
*value*. Its construction collects the loans of its borrow arguments; results
derived from it (like `next()` returns) carry provenance through it to the
original sources. This is the same machinery that already tracks `Borrowed`
view types like `Substring`, generalized.

The core-module early-return in `check_borrow_storage` is deleted. Core's
iterator structs become legal under the general rule, and user-defined
borrowed iterators become possible.

## Protocol contract

```talk
protocol Iterator {
    associated Element
    mut func next() -> Element?
}

protocol Iterable {
    associated Element
    associated Iter: Iterator where Iter.Element == Element
    func iter() -> Iter
}

protocol MutIterable {
    associated Element
    associated Iter: Iterator where Iter.Element == Element
    mut func iter_mut() -> Iter
}

protocol ConsumingIterable {
    associated Element
    associated Iter: Iterator where Iter.Element == Element
    consuming func into_iter() -> Iter
}
```

The `Iter.Element == Element` equality removes the current floating
relationship between an iterable's element and its iterator's element.
`iter()` returns the iterator **by value**; the iterator *stores* any borrow
of the source. (`func iter() -> &T` — returning a borrow of a freshly
constructed iterator — is unrepresentable and was the failure mode of an
earlier core migration attempt.)

Mode selection: plain `for` requires `Iterable` and shared source access;
`mut` requires `MutIterable` and an exclusive place; `consume` requires
`ConsumingIterable` and an owned place/value. The marker never changes what
`next()` yields — that is always the selected iterator's `Element`; the
marker selects which conformance and which source access are required.

Array conformances:

```talk
extend Array<Item>: Iterable           { ... }  // Element == &Item
extend Array<Item>: MutIterable        { ... }  // Element == &mut Item
extend Array<Item>: ConsumingIterable  { ... }  // Element == Item
```

`iter_mut()` performs the CoW make-unique barrier once up front; afterwards
`&mut Item` projections into the unique buffer are sound while the exclusive
loan on the array is live. The consuming iterator owns the buffer, moves
elements out, and its deinit drops the un-yielded tail (early `break`) and
frees the buffer without double-dropping moved-out elements.

String iteration continues to yield `Character` (the borrow-carrying view
type).

### Iterator adapters

Adapters that store the upstream iterator consume it:

```talk
extend Iterator {
    consuming func map<U>(consume fn: (Self.Element) -> U) -> Map<Self, U>
    consuming func skip(count: Int) -> Skip<Self>
}
```

`map` stores the callback (so the parameter is `consume`) and the upstream
iterator (so the receiver is `consuming`). No adapter silently stores `&Self`
through a shared receiver.

## `for` semantics

```text
enter for scope
  source_place = materialize source if rvalue (scoped to the whole loop)
  check source access per marker (shared / exclusive / consume)
  iterator_place = hidden mutable place from iter()/iter_mut()/into_iter()
  loop header:
    next_value = access(iterator_place, Exclusive).next()
    switch next_value:
      some(payload):
        enter iteration scope
          bind user pattern from payload   // typed exactly as Element
          body
        exit iteration scope               // per-iteration drops of owned binders only
        continue
      none:
        break
  drop iterator_place
  drop source_place if hidden
exit for scope
```

This is not a source desugar: it is `CheckedMir` construction from a typed
`For` node. The body sees the user's pattern binding, not synthetic match
binders. A binder whose `Element` is a borrow structurally receives no owned
scope-exit drop — the double-free class loses its generating mechanism rather
than its symptoms. `break`/`continue` use the ordinary target-relative
early-exit drop machinery.

## Type checker product

The checker types `for` first-class: the implicit `iter()`/`next()` (and
mut-mode `write_back()`/`finish()`) calls resolve through the ordinary
member/call machinery at checker-minted node ids, and the binder is
`.some`'s payload via the deferred-variant machinery (no compiler knowledge
of Optional). The resolved ids and finished types are published as a
`ForPlan` keyed by the statement.

**The plan never crosses to lowering.** The typed-tree build (`build.rs`)
consumes it, elaborating the statement into ordinary typed nodes — the same
program Rust's HIR desugar would produce, built once so every later pass
(liveness, flow, MIR, lowering) sees real code:

```text
{                                       // scope: hidden locals die here
    let __for_src = <source>            // rvalue/consume/mut sources only
    let __for_iter = <recv>.iter()      // into_iter/iter_mut by mode
    loop {
        match __for_iter.next() {
            .some(pattern) -> { <body> [__for_iter.write_back(pattern)] },
            .none -> break
        }
    }
    [<source> = __for_iter.finish()]    // mut: take-and-restore
}
```

The calls are rebuilt at the plan's ids, so member resolutions and
instantiations bake onto the nodes exactly like source-written calls; the
elaborated structural nodes (patterns, arms, blocks) get fresh ids from a
descending mint that continues below the checker's (parser ids ascend, so
the ranges never meet). Downstream there is no `for`: MIR lowers a
`Loop`/`Match`/`Let`/`Assignment` like any other, flow checks them like any
other, and celling sees the `next()` receiver and the restore assignment
through its generic scans. The one annotation that survives is
`source_mode` on the hidden source's `Let` (flow's consume/mut source
checks read it off the resulting MIR `Bind`).

A `for` whose selected conformance's receiver mode disagrees with the
marker (e.g. plain `for` finding only a consuming `iter`) is a type error
with a diagnostic recommending the right marker.

## Manual iterator use

Manual use and `for` share one semantics:

```talk
let it = xs.iter()
let first = it.next()
```

`it.next()` is an exclusive access to the local iterator place. A borrowed
`first` carries provenance through `it` to `xs`. `for` must not be correct
only because it has a special lowering; the special part of `for` is scope
construction, not a separate ownership model.

## Implementation stages

The suite must be green after every stage. Tests that currently fail are
written with the stage that fixes them, never landed failing.

1. **Regression matrix.** Named and rvalue sources; nested droppable
   elements; `break`/`continue` dropping per-iteration binders; manual
   `it.next()`; two coexisting shared iterators over one array; matching a
   borrowed loop element without moving it; `self.inner.next()` inside
   `mut func` accepted; the same call through `inner: &Inner` rejected;
   callbacks with borrowed vs consuming parameters; evaluator and VM parity
   with allocation balance.
2. **Access-aware receiver checking.** (Implemented 2026-07-08; smaller than
   drafted.) The access model largely existed: typing's perm unification
   already rejects a direct `&Inner` receiver for a `mut func`, and flow's
   place/loan machinery covers assignment upgrades. The one genuine hole was
   exclusive access through a *projected* place whose root is a shared
   borrow (`outer.inner.bump()` with `outer: &Outer` — the projection types
   as owned `Inner`, so unification cannot see it). Fixed by
   `check_exclusive_root` in flow: an exclusive receiver/argument requires a
   place whose root is not a shared borrow; `rebased_perm`'s cap remains for
   exclusive touches of owned borrow-containing locals (an iterator
   advancing its own cursor). No new `AccessKind`/`CallPlan` layer was
   needed.
3. **General borrow-containing struct rule.** Provenance through construction
   and through `next()` returns (including `Optional<&T>` payloads through
   match peeling). Delete the core exemption in `check_borrow_storage`.
4. **First-class `For`, shared mode.** Carry `StmtKind::For` through name
   resolution, typing (publish `ForPlan`), formatter, and LSP. Delete
   `src/desugar/lower_for_loops.rs` and tests asserting the synthetic AST
   shape. Semantics initially unchanged. (Revised 2026-07-08 after landing:
   lowering originally rebuilt the plan's calls as synthetic typed AST inside
   the MIR builder — a shadow desugar split across parser-minted ids, a plan
   side-table, and per-pass peepholes. The elaboration now happens once in
   the typed-tree build; the MIR builder's `lower_for`, its synthetic-node
   factory, and the liveness/celling/handler-scan `For` special cases are
   all deleted, and the parser mints no checker ids.)
5. **Protocol cleanup.** `Iter.Element == Element`; adapters take consuming
   receivers and store upstream iterators by value; migrate Array, String,
   Substring.
6. **Consuming iteration.** (Implemented 2026-07-08, v1.) The `consume`
   marker in iterable position; typing selects `into_iter`; the source is
   always moved into the hidden source binding, and flow rejects sources
   reached through borrows or used again after the loop (no silent clone).
   `ArrayIntoIterator` owns the array. V1 residual: it still yields
   *borrowed* elements. Owned yields are blocked on a design decision —
   generic `&T → T` has no duplication witness (the tier-2 clone coercion
   fires only for concrete Copy/CheapClone nominals), and moving out via a
   raw load double-frees now that `Array: Deinit` deep-drops elements.
   Chosen direction (2026-07-08): per-θ generic clone coercion at argument
   positions. Attempting it surfaced a deeper pre-existing gap that blocks
   it: a bare `&T` **call result cannot be bound, returned, or passed as a
   value at all** — even `let e: &String = xs.get(0)` is a type error on
   main today. Borrow-typed results only work as receivers of further
   calls, through `Optional<&T>` payloads (match binders), or where the
   Copy/CheapClone coercions erase them. Making borrow-typed results
   first-class values is prerequisite work for both the coercion and for
   stage 7's `&mut` element yields, and needs its own design pass.
7. **Exclusive iteration.** (Implemented 2026-07-08, take-and-restore v1.)
   `for x in mut xs` moves `xs` into `iter_mut()`'s owning iterator,
   yields owned elements, binds them to an assignable binder, appends a
   `write_back(consume value)` call after each iteration body, and
   restores the source at loop end via `xs = iterator.finish()` — an
   ordinary assignment, so flow models the whole loop as move-then-restore
   and the source is usable afterwards. This is mutable value semantics
   (the same copy-in/write-back paradigm as `mut` parameters), not `&mut`
   projection: runtime borrows are erased, so a pointer-shaped
   `&mut Element` cannot exist as a value. The typed extras
   (`write_back`/`finish` resolutions, the binder-read argument node) ride
   the `ForPlan` under checker-minted ids into the elaboration;
   `Array._replace` releases the overwritten element. V1 limits: the source must be an assignable
   variable, the binder a single name, and `break`/`continue` skip that
   iteration's write-back.

Also implemented alongside stage 6/7 (2026-07-08): **first-class
borrow-typed call results** — `let e: &String = xs.get(0)`, returning
`&T`, and passing borrow results now work. The failures were ordering
bugs, not a missing feature: checking-mode expected types eagerly bound a
call's unresolved result var before member resolution revealed the
scheme's borrow-typed return. Fixed by deferral throughout —
`emit_immediate_borrow_check` defers unresolved founds under every reason
(via `ApplyBorrow`), and a new `CoerceOwned` constraint defers owned
slots fed borrow-or-unsolved arguments, resolving to the per-instantiation
clone coercion (`Param` or Copy/CheapClone expected) or the plain
equality. En route, a latent runtime bug: `retain_then` walked the
un-erased borrow type, so tier-2 clones of borrow-typed *arguments* never
emitted their retain (double free); it now erases the borrow before the
retain walk.

### Discovered pre-existing defects (reproduced on clean HEAD — all FIXED)

Reduced from stage-7 verification; none was caused by this ADR's work.
All three are fixed, each with a regression test:

- **Celled-array drops leaked** (`vm_mutated_array_local_drops_balanced`):
  `let xs = [5]` then `xs.push(6)` leaked two allocations. Two roots:
  borrowed parameters were never seeded initialized, so the
  `AssignmentReplace` drop for `self.storage = fresh` classified Dead and
  the old buffer never released (`seed_params` now restores borrowed
  roots); and `uniqued_storage() -> &mut Storage` tier-2-cloned its
  return value (+1 retain nothing released) because the return check
  used the value's type, not the function's borrow return type
  (`ret_is_borrow` in `check_body`).
- **Reassigned shared arrays crashed the VM**
  (`vm_reassigned_shared_array_keeps_sharer_alive`): `let ys = xs` then
  `xs = [7]` died with "load of a bad arena handle". The dynamic drop
  path's deinit dispatch used `nominal_theta` (witness generics unbound —
  element loads ran erased and read an Int payload as a handle) and
  skipped structural teardown; it now matches the static path
  (`deinit_theta` + `lower_structural_teardown_then`).
- **Borrow-typed match binders from owned scrutinees never registered**
  (`vm_consuming_protocol_default_on_borrowed_projection`): exposed by
  the honest refcounts above. `seed_arm_binders` read binder types from
  `node_types` (keyed by node id — empty for pattern binders) instead of
  `local_tys` (keyed by symbol), so under an owned scrutinee that merely
  contains borrows (`Optional<&T>` from `next()`) a `&T` binder never
  installed its provenance, and extracting a field out of it silently
  moved instead of tier-2 cloning — the consuming callee's release plus
  the array's deep-drop double-freed the buffer. Previously masked by
  the `uniqued_storage` over-retains keeping element buffers non-unique
  so `Array.deinit` skipped deep-drops.

## Deletions

The measure of done — mechanisms, not symptoms:

- `src/desugar/lower_for_loops.rs` and its synthetic naming scheme;
- the `ModuleId::Core` exemption in `check_borrow_storage`;
- ad-hoc receiver borrow unification replaced by access checking;
- the loop-binder-typed-owned workarounds and (with no synthetic match/temps
  in loop bodies) the ADR 0017 temp-drop drain class;
- any test asserting the desugared AST shape.

## Non-goals

- No full collection hierarchy.
- No `copy foos` iteration semantics decision (it parses under the marker
  grammar; v1 may reject it with a targeted diagnostic).
- No change to ADR 0018's parameter defaults.
- No removal of explicit `&T` as a type constructor.

## Consequences

- `for` becomes a deep module: source lifetime, iterator lifetime, element
  ownership, provenance, and drop order sit behind one checked construct.
- The call checker becomes the single authority on access; later phases read
  plans instead of reinterpreting syntax.
- Iterator implementers state whether they yield borrowed, exclusive, or
  owned elements; adapters own their upstream iterators.
- Code that accidentally relied on owned array iteration needs an explicit
  `copy` or `consume`.

## Relationship to earlier ADRs

- **ADR 0018:** the iterable position reuses call-site markers and the
  borrow-by-default access vocabulary; plain iteration is quiet, transfer is
  explicit.
- **ADR 0019:** `for` is elaborated at the `TypedProgram` build, so the
  `TypedProgram`/`CheckedMir` seam carries only ordinary constructs;
  `ForPlan` is a checker-published fact consumed by that build alone.
- **ADR 0017:** rvalue iterable lifetime becomes a structural `CheckedMir`
  fact; the temp-drop drain bug class loses its generating mechanism.
- **ADR 0016:** `Iterator.Element` and `Iterable.Element` remain associated
  outputs; the new equality ties them together.
