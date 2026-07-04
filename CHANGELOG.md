# Changelog

## Unreleased (2026-07-03)

Talk's memory story is rebuilt end to end. Ownership lives in the type
system — permissions and grades, with a small flow pass for the
flow-sensitive questions — and `'heap` structs add mutable aliased
structures with all management inferred. No lifetime annotations, no
manual frees. Effect handlers grew up alongside it: dynamic extent,
inferred effect rows, unhandled-effect errors, and generic effects,
compiled capability-passing with zero-cost tail resumes.

### Ownership and borrowing

- **Declaration grades, in tick-suffix position** — `struct Token 'linear
  { ... }` declares a must-consume type: every value has to reach a
  consuming use (a move, a `consuming func`), and letting one go out of
  scope unconsumed is an error. Linear types cannot conform to `Deinit`.
- **`Copy` marker protocol** — user types opt into copy semantics
  (`extend Point: Copy {}`); conformance is validated structurally, so a
  type holding owned data cannot claim it. Scalars (`Int`, `Float`,
  `Bool`, `Byte`, `Void`) are `Copy` intrinsically, and **borrows of
  `Copy` types erase**: `&Int` and `Int` are interchangeable everywhere —
  `sum = sum + arr.get(j)` just works, and a protocol method on `Int` can
  return owned `self`.
- **`CheapClone` marker protocol and silent clones** — types whose clone
  is an O(1) refcounted-buffer retain (`String`, `Array`, `Storage`,
  `ByteStorage`). Where an owned `CheapClone` value is needed but only a
  borrowed one is available, the compiler clones silently instead of
  erroring: extracting an owned field from a borrowed value
  (`person.name` from `person: &Person`), or passing a `&String` to a
  `String` parameter. Non-`CheapClone` types still report "cannot move
  out of borrowed value".
- **Unique types `*T`** — a value that is statically the sole reference
  to its contents. Unique values always move (never copy, never silently
  clone) and can be mutated in place without runtime checks.
- **`Deinit` protocol (destructors)** — conform with a
  `consuming func deinit()` and it runs when the value drops at scope
  exit. Drops run in reverse declaration order; values moved on only some
  paths get drop flags so they drop exactly once. Owned enum payloads,
  consumed by-value arguments, match-arm payload binders, tail-position
  branches, and existential payloads (with their destructors) all drop.
- **Borrows end at last use (NLL), with no lifetime annotations — ever.**
  Where a returned borrow may point is inferred interprocedurally:
  borrows derived from parameters can be returned; returning a borrow of
  a function-owned value — bare or smuggled inside a wrapping struct —
  is an error (unless the silent-clone rule applies).
- **Storage rules** — a `&T` in a struct field or enum payload is a
  compile error; borrowed *view* types like `Substring` are fine to
  store, and the checker tracks the borrows they carry. A global may hold
  borrows only of other globals (`let it = numbers.iter()` at the top
  level is legal), and those owners become unassignable everywhere:
  `Cannot assign to global 'numbers': global 'it' borrows it`.
- **Closure captures are fully inferred** per variable (read → shared
  borrow, mutate → exclusive borrow, consume/escape → move). Explicit
  capture lists remain as overrides.
- **Copy-on-write `Array`** — `Array.set` is a `mut func`: it requires
  exclusive access, and if the element buffer is shared it copies before
  the first write. Arrays keep value semantics even when clones share
  storage. (`_is_unique(ptr)` core intrinsic and the `is_unique`
  inline-IR instruction expose the refcount test.)
- **Runtime allocations are refcounted.** Freeing is a release, silent
  clones retain, and every allocation is released by scope-exit drops —
  programs end with no live allocations.
- **Inference works with the grain of the checker**: matching on an
  unannotated borrowed-element result (`let opt = it.next()`) resolves
  the enum from the pattern's variant names; `let r: Optional<Int> =
  it.next()` accepts an iterator over borrowed elements.
- **Ownership errors are phrased as operations**, e.g. "Use of moved
  value 'x'", "Cannot move 'x' while it is borrowed as 'y'", "'f' is
  linear and must be consumed exactly once; it would be dropped here".
- **Editor support** — inlay hints mark every silent clone (` clone`,
  with an "O(1) buffer retain" tooltip) alongside move/borrow/drop hints;
  hover classifies types as `owned`, `copy`, `borrowed view`,
  `linear (must be consumed)`, `cheap to clone (buffer retain)`, and
  shows `shared borrow of T` / `mutable borrow of T` for `&T`/`&mut T`.

The `Owner` and `Borrowed` marker protocols remain in `core/Ownership.tlk`
and are still honored, but new code should rarely need them: ownership
classification is otherwise derived from a type's structure and grade.

### `'heap` structs and inferred regions

- **`'heap` structs (reference semantics).** `struct Node 'heap { ... }`:
  variables hold references — assignment aliases, mutation through one
  reference is visible through all, cross-links and cycles are fine, and
  `mut func` receivers mutate in place (no copy-back). Everything else
  keeps copy-on-write value semantics.
- **Inferred regions underneath.** Every heap value lives in a region;
  linking values merges their regions; a region is torn down — `Deinit`
  destructors in reverse allocation order, then one bulk free — when the
  last binding referencing into it goes out of scope. **Cycles never
  leak.** Regions behave like arenas: unlinking never frees early.
  Storing a heap reference anywhere during teardown is a runtime error.
- **Reading an owned value out of a heap struct clones it** (the same
  silent CheapClone rule as borrowed-field extraction): `node.name` hands
  you an independently-owned `String` backed by the same buffer. Generic
  fields extract per instantiation: CheapClone types clone, copy types
  copy, and owned non-CheapClone instantiations are compile errors.
- **`Dict<Value>` in core** — a growable string-keyed dictionary built on
  a heap node chain (`insert`/`get`/`count`); a placeholder for a hash
  table.
- **The HTTP router is growable**: `HttpServer` is `'heap`, and routes
  live in a chain — the old four-route cap is gone.
- **LSP**: hover on `'heap` types shows `heap — reference semantics,
  region-allocated`.

### Effect handlers (dynamic extent)

Effects went from lexically-routed sketch to the real thing: handlers
reach through calls, effects are inferred, and generic effects work end
to end. Compiled capability-passing style (ADR 0011); no runtime handler
search.

- **Handlers cover their dynamic extent.** `@handle 'throw { err in
  print(err) }` covers everything sequenced after it — including
  performs inside functions it calls, however deep. A handler body that
  finishes **aborts** the handled scope with its value; `continue v`
  **resumes** the perform with `v` — in any expression position, across
  call frames (one-shot). Nearest handler wins; an inner same-effect
  handler covers the whole label (an outer one never fires for it).
- **Effects are inferred.** An unannotated function's latent effects ride
  its row (rendered `! <'throw>`); explicit annotations (`func f()
  'throw -> ()`, `'[]`) stay as checked bounds. `examples/Throwsies.tlk`
  — handler in the caller, unannotated performer — runs as written.
- **Unhandled effects are compile errors.** A user effect reaching the
  top level reports `No handler for 'e` at the node where it escapes —
  position-aware, so calling an effectful function *before* its
  top-level `@handle` is the same error. Only the core effects (`'io`,
  `'async`, `'alloc`) are implicitly handled by the runtime.
- **Generic effects.** `effect 'state<T>(value: T) -> T` handles like
  anything else: rows carry instantiations (`! <'state<Int>>`), and one
  `@handle 'state` covers *every* instantiation flowing through its
  extent — the handler body is generic over `T` (declared bounds like
  `T: Showable` apply), and each instantiation gets its own specialized
  capability behind the scenes.
- **Function values capture their handlers.** Function literals and
  trailing blocks keep the capabilities of their creation site (so an
  effectful closure passed to a higher-order function works), and a
  named effectful function used as a value wraps itself over the
  handlers in scope.
- **VM support: one-shot continuations.** Aborts unwind by reified
  continuation (`MakeCont`/`CallCont`) instead of a threaded calling
  convention; a handler that escapes its scope and then aborts traps
  cleanly ("continuation is no longer live") — an escaped *resuming*
  handler still works.

Effects v1 limits: a perform inside a function literal routes to the
handlers at the literal's **creation** site, not its call site (they
coincide in the usual HOF pattern); no masking past an inner same-effect
handler; resume is one-shot; and an abort skips the drops of the frames
it unwinds (the same teardown fence tracked under Testing).

### `'heap` v1 limits (compile errors)

- A heap reference captured by an escaping closure.
- A heap struct packed as `any P`.
- Heap types inside raw-storage containers (`Array<Node>`).
- `'heap` combined with `'linear`, `Copy`, or `CheapClone`.
- Auto-derived `Showable` for `'heap` structs (a structural walk would
  cycle on graphs) — write an explicit conformance.

### Fixed

- **`for x in xs { x in … }` (a body block with its own argument) works.**
  The desugar bound the block argument as a second, never-reseeded
  symbol, so the body's argument was untyped and a `match` on it reported
  a false "Use of moved value" on every iteration after the first.
- **Matching variant patterns on iterator elements works.** Iterating a
  container yields borrowed elements; variant patterns on a scrutinee
  whose element type was still being inferred pinned it to the owned enum
  ("expected &E, found E"). Pattern matching now looks through the borrow
  once the element type resolves — `for e in items { match e { .a(x) ->
  … } }` is usable for any enum container.
- **Matching a borrowed enum no longer double-frees its payloads.** Arm
  binders over a borrowed scrutinee are aliases; they no longer drop
  values the owner still holds, and moving a payload out routes through
  the silent-clone rule (or errors) instead of silently consuming the
  owner's buffer.
- **`as` expressions run.** `1 as Int` and packing ascriptions like
  `41 as any Number` previously failed to lower ("expression not yet
  supported"); the coercion now erases at the HIR boundary and the
  ascribed pack applies to the value.
- **The formatter's multiline labeled calls now re-parse.** Argument
  lists accept newlines between arguments (and a trailing comma before
  `)`), so formatting a long labeled call no longer produces unparseable
  code.
- **`typealias` formats with spaced `=`** (`typealias Target = Response`,
  not `Target=Response`).

### Compiler internals

The middle end is rebuilt around a small core (the strangler arc of the
core-IR plan, C1–C6):

- **A desugar phase** runs between parsing and name resolution
  (`src/desugar/`): for-loops, operators, `func`-to-`let`, method `self`,
  and expression-`if` → boolean `match` all collapse before any analysis
  runs; the name resolver only binds names.
- **The HIR is Core-shaped.** Literal forms merged, `as` and
  parenthesization erased at build, stored-field reads (`Proj`) and
  variant constructions (`Con`) split from `Member`/`Call` by the
  checker's resolutions — every type-directed classification happens
  once, at HIR build, instead of per analysis.
- **Flow analysis is pure CFG dataflow** (ADR 0010 completed): handler
  bodies and trailing blocks are basic blocks with may-execute edges; the
  tree-walking checker is deleted. `break`/`continue`/`return` are edges,
  conditional-path moves join correctly at loop heads, and early-exit
  drops are target-relative.
- **MIR statements are evaluation units.** Matches lower through
  value-carrying join points, and calls/performs evaluate at their own
  statements with results flowing through temporaries — expression trees
  embedded in statements are straight-line and pure. (The former
  statement-spine splitter for abortable calls is gone entirely — in
  CPS every expression has a continuation, so performs need no special
  position.)
- **Effects compile capability-passing (ADR 0011).** Functions take one
  capability parameter per user-effect instantiation in their inferred
  row (the zonked scheme rows are the single routing truth — the
  resolver's lexical handler routing, the checker's four capability side
  tables, and the whole abort-capable calling convention are deleted).
  `@handle` holds a capability *template*; closures materialize per
  instantiation with the effect's generics bound in θ — the
  generic-function specialization machinery applied to a handler block.
  Effect rows carry instantiations as inert entries (duplicate labels
  allowed, arguments never unified across entries); `@handle` is a
  label-scoped elimination constraint processed at solve quiescence
  (docs/generic-effects-plan.md).
- **`lower/` is decomposed by concern** (demand/monomorphization,
  functions, matches, values, closures, calls, effects, splices, θ).

### Testing

- **Leak detection is suite policy.** Every program-running test executes
  on the allocation-tracking evaluator and asserts that allocations and
  `'heap` objects balance to zero at exit (scalar-valued programs; a
  program whose value carries buffers legitimately holds them). The known
  deficit — containers do not yet tear down their elements' buffers, and
  the builtin io path does not drop its by-value arguments — is fenced by
  the greppable `eval_expecting_container_element_leak`, deleted when
  element teardown lands (the buffers are already refcounted; teardown is
  an element-release loop at last release).
- **A real-program corpus** (`tests/programs/`): small, complete,
  idiomatic programs (iterate-and-match, string building, conditional
  moves in loops, `'heap` graphs, and an effects battery — caller-locals
  handlers, nested same-effect handlers, cross-frame resume,
  multi-effect threading, effectful closures, generic effects at one and
  several instantiations) checked and run on both engines with stdout
  equality under the balance policy.
