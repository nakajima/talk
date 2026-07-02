# Changelog

## Unreleased (2026-07-02)

Talk's memory story is rebuilt end to end. Ownership lives in the type
system — permissions and grades, with a small flow pass for the
flow-sensitive questions — and `'heap` structs add mutable aliased
structures with all management inferred. No lifetime annotations, no
manual frees.

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

### v1 limits (compile errors)

- A heap reference captured by an escaping closure.
- A heap struct packed as `any P`.
- Heap types inside raw-storage containers (`Array<Node>`).
- `'heap` combined with `'linear`, `Copy`, or `CheapClone`.
- Auto-derived `Showable` for `'heap` structs (a structural walk would
  cycle on graphs) — write an explicit conformance.

### Fixed

- **The formatter's multiline labeled calls now re-parse.** Argument
  lists accept newlines between arguments (and a trailing comma before
  `)`), so formatting a long labeled call no longer produces unparseable
  code.
- **`typealias` formats with spaced `=`** (`typealias Target = Response`,
  not `Target=Response`).
