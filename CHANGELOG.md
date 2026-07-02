# Changelog

## Unreleased — heap structs and inferred regions (2026-07-02)

Talk can now express mutable aliased structures — graphs, doubly-linked
lists, parent pointers, growable tables — through one new declaration
attribute, with all memory management inferred.

### Added

- **Tick-suffix declaration attributes** are now *the* modifier position:
  `struct Node 'heap { ... }`, `struct Token 'linear { ... }`. The old
  `linear struct` prefix no longer parses (the error points at the new
  form).
- **`'heap` structs (reference semantics).** Variables hold references:
  assignment aliases, mutation through one reference is visible through
  all, cross-links and cycles are fine, and `mut func` receivers mutate in
  place (no copy-back). Everything else keeps copy-on-write value
  semantics.
- **Inferred regions underneath.** Every heap value lives in a region;
  linking values merges their regions; a region is torn down — `Deinit`
  destructors run in reverse allocation order, then one bulk free — when
  the last binding referencing into it goes out of scope. **Cycles never
  leak.** Regions behave like arenas: unlinking never frees early.
  Storing a heap reference anywhere during teardown is a runtime error.
- **Owned values read out of a heap struct clone** (the same silent
  CheapClone rule as borrowed-field extraction): `node.name` hands you an
  independently-owned `String` backed by the same buffer.
- **`Dict<Value>` in core** — a growable string-keyed dictionary built on
  a heap node chain (`insert`/`get`/`count`); a placeholder for a hash
  table.
- **The HTTP router is growable**: `HttpServer` is now `'heap`, and
  routes live in a chain — the old four-route cap is gone.
- **LSP**: hover on `'heap` types shows `heap — reference semantics,
  region-allocated`.

### Fixed

- **Enum payloads now drop.** An `Optional<String>` (or any enum with owned
  payloads) frees its payload at scope exit, on assignment replace, and on
  conditional paths (drop flags) — previously payloads silently leaked.
- **Consumed by-value arguments now drop in the callee.** Passing an owned
  value to a function leaked its buffers before; the parameter now drops at
  the callee's exit (and a `consuming func`'s self discharges linearity as
  the value's intended end).
- **Match-arm payload binders drop** (`.some(s) -> ...` frees `s`'s owned
  payload once — the consumed scrutinee is dead, so exactly once).
- **Drops now reach tail-position branches.** `if`/`match` in tail position
  with a consuming branch previously skipped the other branch's scope-exit
  drops entirely.
- **Existential payloads drop — including destructors.** Every `any P`
  value carries a drop witness; the packed value's owned buffers free and
  its `Deinit` runs when the existential goes out of scope. (Generic
  repacks — packing a bare type parameter — still defer their payload
  drop.)
- **Auto-derived `Showable` is rejected for `'heap` structs** — a
  structural walk would cycle on graphs; write an explicit conformance.
- **The region ledger balances everywhere**: destructuring lets, rvalue
  match scrutinees, and rvalue arguments through closure, protocol, and
  existential calls all release their regions correctly.
- **The formatter's multiline labeled calls now re-parse.** Argument lists
  accept newlines between arguments (and a trailing comma before `)`), so
  formatting a long labeled call no longer produces unparseable code.
- **`typealias` formats with spaced `=`** (`typealias Target = Response`,
  not `Target=Response`).
- **Generic extraction from heap structs.** Reading an owned field whose
  type is a generic parameter out of a `'heap` struct now works per
  instantiation: CheapClone types clone (buffer retain), copy types copy,
  and owned non-CheapClone instantiations are reported at compile time.
  `Dict<String>` is fully supported.

### v1 limits (compile errors)

- A heap reference captured by an escaping closure.
- A heap struct packed as `any P`.
- Heap types inside raw-storage containers (`Array<Node>`).
- `'heap` combined with `'linear`, `Copy`, or `CheapClone`.

## Unreleased — ownership redesign (2026-07-02)

The memory-management story was rebuilt from scratch: ownership now lives in
the type system (permissions and grades) with a small flow pass for the
flow-sensitive questions, replacing the old standalone checker. Most programs
that compiled before still compile; the changes below are what you can
observe from the language.

### Added

- **`linear` declaration modifier** — `linear struct FileHandle { ... }`
  declares a must-consume type: every value has to reach a consuming use
  (a move, a `consuming func`), and letting one go out of scope unconsumed
  is an error. Linear types cannot conform to `Deinit`.
- **Unique types `*T`** — a value that is statically the sole reference to
  its contents. Unique values always move (never copy, never silently
  clone) and can be mutated in place without runtime checks.
- **`Deinit` protocol (destructors)** — conform with a
  `consuming func deinit()` and it runs automatically when the value is
  dropped at scope exit. Drops run in reverse declaration order; values
  moved on only some paths get drop flags so they are dropped exactly once.
- **`Copy` marker protocol** — user types can opt into copy semantics
  (`extend Point: Copy {}`); conformance is validated structurally, so a
  type holding owned data cannot claim it. Scalars (`Int`, `Float`, `Bool`,
  `Byte`, `Void`) are `Copy` intrinsically.
- **`CheapClone` marker protocol and silent clones** — types whose clone is
  an O(1) refcounted-buffer retain. `String`, `Array`, `Storage`, and
  `ByteStorage` conform. Where an owned `CheapClone` value is needed but
  only a borrowed one is available, the compiler clones silently instead
  of erroring:
  - returning, binding, or passing an owned field out of a borrowed value
    (`person.name` from `person: &Person`);
  - passing a `&String` where a `String` parameter is expected.
  Non-`CheapClone` types still report "cannot move out of borrowed value".
- **Copy-on-write `Array`** — `Array.set` is now a `mut func`: it requires
  exclusive access, and if the element buffer is shared with another array
  it copies the buffer before the first write. Arrays keep value semantics
  even when clones share storage.
- **`_is_unique(ptr)` core intrinsic** and the `is_unique` inline-IR
  instruction (`%? = is_unique $0`) — true when an allocation's refcount
  is 1; static data is never unique.
- **Editor support for the new semantics**:
  - inlay hints mark every silent clone (` clone`, with an "O(1) buffer
    retain" tooltip) alongside the existing move/borrow/drop hints;
  - hover classifies types as `owned`, `copy`, `borrowed view`,
    `linear (must be consumed)`, and `cheap to clone (buffer retain)`,
    and shows `shared borrow of T` / `mutable borrow of T` for `&T`/`&mut T`.

### Changed

- **Borrows end at last use (NLL), with no lifetime annotations — ever.**
  Where a returned borrow may point is inferred interprocedurally; borrows
  derived from parameters can be returned, and returning a borrow of a
  function-owned local is an error (unless the silent-clone rule above
  applies).
- **Drop timing is scope exit**, reverse declaration order — not last use.
- **Closure captures are fully inferred** per variable (read → shared
  borrow, mutate → exclusive borrow, consume/escape → move). Explicit
  capture lists remain as overrides.
- **Borrows cannot be stored**: a `&T` in a struct field, enum payload, or
  global is a compile error — borrows end with their owner's scope.
  (Borrowed *view* types like `Substring` are still fine to store.)
- **Runtime allocations are refcounted.** Freeing is a release (the buffer
  dies when the last owner releases it), silent clones retain, and every
  allocation is released by scope-exit drops — programs end with no live
  allocations.
- **Ownership errors are phrased as operations**, e.g. "Use of moved value
  'x'", "Cannot move 'x' while it is borrowed as 'y'", "'f' is linear and
  must be consumed exactly once; it would be dropped here".

The `Owner` and `Borrowed` marker protocols remain in `core/Ownership.tlk`
and are still honored (`Substring` and friends are recognized as borrowed
views through `Borrowed`), but new code should rarely need them: ownership
classification is otherwise derived from a type's structure and grade.
