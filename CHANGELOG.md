# Changelog

## Unreleased (2026-07-04) — Protocol arguments in conformance keys

Protocol applications now participate in conformance identity. A
conformance is selected by the full protocol reference, not only by the
protocol symbol, so one type can soundly provide multiple conformances to
the same protocol family with different input arguments:

```talk
protocol Add<RHS> {
	associated Ret
	func add(rhs: RHS) -> Ret
}

extend String: Add<String> { ... }
extend String: Add<Character> { ... }
```

The design boundary is now explicit:

```text
protocol arguments = inputs to conformance selection
associated types   = outputs of selected conformance
```

Associated-type projections are therefore keyed by the selected full
protocol application, e.g. `<Self as Add<RHS>>.Ret`, while `RHS` is an
input used to choose that application. This preserves coherent,
deterministic witness selection without relying on conformance table
order. Duplicate or overlapping full conformance keys remain errors, and
member uses whose protocol arguments cannot be determined report
ambiguity instead of picking an arbitrary row.

Conformance rows can now bind protocol-argument-only parameters with
prefix extend generics:

```talk
extend<T: Into<String>> String: Add<T> {
	func add(other: T) -> String { self + other.into() }
}
```

This row means `forall T. T: Into<String> => String: Add<T>`. Rows that
can overlap an existing conformance pattern are rejected for now; a later
specialization design can make those preferences explicit.

Core operator protocols were migrated to this model:

- `Add<RHS>`, `Subtract<RHS>`, `Multiply<RHS>`, and `Divide<RHS>` keep
  `Ret` as an associated output.
- `Equatable<RHS>` and `Comparable<RHS>: Equatable<RHS>` now use the
  compared type as a protocol input.

The checker/lowerer now also carries a first-class `ProtocolApplication`
for `Self: Protocol<Args...>` requirement instantiation, so protocol
`Self`, protocol inputs, and associated projections are bound as one
semantic operation rather than loose substitution plumbing.

Protocols whose result/member type is determined by the conforming type,
such as `Iterator.Element`, should continue to use associated types.
See `docs/adr/0016-protocol-argument-conformance-keys.md` and
`docs/protocol-arguments-vs-associated-types.md` for the design rationale.

## Unreleased (2026-07-04) — Leading-dot variants in inference position

`.variant` and `.variant(args)` no longer require the expected enum to
be known at the use site's syntax. When the enum arrives through
unification — a generic call's argument, a binder typed by later use —
resolution defers to the constraint solver (the same discipline as
member access on an unknown receiver):

```talk
enum Maybe<T> { case some(T), none }
func id<T>(x: T) -> T { x }
let m: Maybe<Int> = id(.some(42))   // previously: unsupported
```

A leading dot whose enum is never determined by context reports
"Cannot infer the enum for '.variant'; add a type annotation".

## Unreleased (2026-07-04) — Sequential scoping for locals

Local bindings now follow the standard ML/Rust model: a `let` is
visible from just after its initializer to the end of its block, and
rebinding a name is ordinary shadowing. Module scope (and the REPL's
top-level redefinition) is unchanged. Design and citations:
docs/adr/0013-sequential-scoping-for-locals.md.

### Scoping

- **A binding starts at its initializer, not at block top.** The
  right-hand side of a `let` sees the outer binding, so staged
  initialization reads naturally — and rebinding in the same block is
  legal now (the interim "already declared in this scope" error is
  gone).

  ```talk
  func f(x: Int) -> Int {
  	let x = x + 1     // reads the parameter
  	let x = x * 10    // reads the previous x
  	x                 // 10 * (param + 1)
  }
  ```

- **Using a name before its `let` is an error.** Locals no longer hoist:
  a use before the declaration is `Undefined name`, instead of silently
  resolving to a binding that doesn't exist yet.
- **Closures capture the binding visible where they're written.** A
  later rebinding doesn't retroactively change what an earlier closure
  captured.

  ```talk
  let x = 1
  let g = func() -> Int { x }
  let x = 2
  g() + x               // 3
  ```

- **`func` decls in a block are items** (like Rust's `fn` in a block):
  visible block-wide regardless of order, so local funcs can be
  mutually recursive. A later `let` of the same name still shadows one.
- **Duplicate bindings that would orphan each other still error** — one
  pattern binding a name twice (`(a, a)`), or two same-named local
  `func`s in one block — now worded "declared more than once in this
  scope".

### Recursive local funcs

Local funcs that call themselves (or each other) now compile and run —
previously they resolved but crashed the compiler during lowering, and
a recursive func declared after another `let` failed to type-check.
Recursion works through captures too:

```talk
func outer() -> Int {
	let step = 2
	func down(n: Int) -> Int {
		if n > 0 { down(n - step) + 1 } else { 0 }
	}
	down(6)               // 3
}
```

Local funcs stay monomorphic within their block (recursion doesn't
generalize), matching `let rec` in ML without a signature. A local func
binding that is itself reassigned can't recurse yet; that's a
diagnosed "not yet supported", not a crash.

### Compiler internals

- **Locals resolve in one in-order walk.** The declarer pass shrank to
  module scope and type members; the resolver pass creates block, arm,
  and function scopes fresh as it walks, minting a `let`'s binders at
  the declaration and inserting them when the initializer resolves.
  The per-`let` mini-scopes, their paired enter/exit in both passes,
  and the parent-pointer scope teleporting are deleted
  (docs/adr/0013-sequential-scoping-for-locals.md).
- **The resolver's shadow analyses are gone.** Its capture recording
  and SCC dependency graph (with the per-`let` level bookkeeping) were
  consumed only by the resolver's own tests — the checker runs its own
  dependency analysis and flow computes closure captures. Deleted
  outright (net −396 lines in `name_resolution`); the `Level` type
  moved to `types/`, its real consumer.
- **Every mirror of fn-in-block hoisting is explicit.** The resolver
  hoists func-valued `let` binders at block entry; the checker
  pre-binds them to shared monomorphic variables before checking the
  block; the lowerer pre-mints their λ_G labels at basic-block entry
  and binds a named local func directly to its `func_ref` (no `let_…`
  continuation — through a binder var, mutual funcs would nest under
  each other's lets and cycle the λ_G nesting relation).
- **A missing callable signature can no longer panic the lowerer.**
  `demand` returns `Option<Label>`: callers abandon the construct as a
  diagnosed, well-typed `dead_end` instead of applying a void-domain
  placeholder whose type was a lie (the old `unreachable!` at the λ_G
  T-App check).

## Unreleased (2026-07-04) — Protocol extensions, effect-polymorphic fields, leak-free ownership

Three threads, one day. Protocols grew extension methods, so shared
behavior lives on the protocol instead of every conforming type. Struct
fields that hold closures became effect-polymorphic — one instance
storing an effectful closure no longer taints another. And the ownership
story closed its last gap: the generic-ownership leak fence is deleted,
and every test in the suite now asserts exact allocation balance.

### Protocol extensions

- **`extend P { ... }` adds methods to a protocol.** Extension methods
  behave as defaulted requirements: every conforming type gets them, and
  they dispatch through the conformance like any witness. Iterator
  pipelines compose on any element type:

  ```talk
  let i = [10, 20, 30].iter().skip(1).index(30)   // Optional.some(1)
  for ch in "héllo".iter() { print(ch) }           // h é l l o
  ```

- **Comparisons take their right-hand side by borrow** (`rhs: &RHS`,
  ADR 0014), so `==` and friends never consume their operands; scalar
  witnesses still receive plain values (borrows of `Copy` types erase).

### Effect-polymorphic struct fields

- **A closure stored in one instance no longer contaminates another.**
  A closure-typed field's effect row used to be a single module-wide
  inference variable: constructing one `Wrapper` with an effectful
  closure made an unrelated, pure `Wrapper` demand the same handler.
  Fields' rows are now quantified per struct (implicit effect
  parameters, Koka-style kinded type arguments), instantiated at each
  construction, and recovered at each read:

  ```talk
  struct Wrapper {
  	let f: () -> Int
  }
  effect 'ping() -> Void

  func pure_use() -> Int {
  	let w = Wrapper(f: func() { 1 })
  	w.f()                       // fine — no 'ping here
  }
  func pingy_use() 'ping -> Int {
  	let w = Wrapper(f: func() {
  		'ping()
  		1
  	})
  	w.f()                       // this one performs 'ping
  }
  ```

- **And the effects still travel.** The instance's row rides its type,
  so returning a struct that stores an effectful closure — even across
  a module boundary — still demands the handler at the call site.
  A struct cannot launder an effect. Design and trade-offs:
  docs/effect-params-on-structs-plan.md.

### Leak-free ownership, no exceptions

- **The generic-ownership fence is deleted.** Every program-running test
  — vm differential tests, the examples corpus, the program corpus —
  now asserts that allocations and `'heap` objects balance to zero at
  exit. Generic (type-parameter-typed) values are owned: the last
  consuming use moves, earlier ones implicitly copy per instantiation
  (a retain for refcounted types, free for `Copy`), and unconsumed
  values release at scope exit — decided once over the generic body,
  elided per specialization.
- **Borrowed temporaries are released.** A call result that is only
  borrowed by its consumer (`print("a" + "b")` — `print` takes `&T`)
  now frees at the end of its full expression. Chasing the remaining
  imbalances to zero fixed a family of latent bugs: operators consumed
  receivers their callees only borrowed, empty string statics aliased
  the first heap allocation, and derived `show` leaked every
  intermediate accumulator.
- **Raw allocations can be freed.** `_free(ptr)` releases an `_alloc`
  buffer (one reference; statics are unmanaged), backed by a new
  `@_ir { free $0 }` instruction. `open_path` now frees its
  NUL-terminated path copy, and the raw-io examples free their buffers.

## Unreleased (2026-07-04) — Neovim setup

- **`talk setup nvim` installs the Neovim runtime files.** The CLI
  downloads the bundled `ftdetect`, `ftplugin`, `indent`, and `syntax`
  files from the repository into Neovim's `stdpath('data')/site` runtime
  root, with an XDG/`NVIM_APPNAME` fallback when Neovim is unavailable.
  `--force` overwrites differing TalkTalk runtime files, and
  `--target-dir` installs into an explicit runtime root. The Neovim README
  now points users at this command; adding the runtime directory to
  `runtimepath` remains the development setup.
- **`TALK_CORE_PATH` can override the bundled core library.** Set it to a
  directory containing the core `.tlk` files and the `talk` executable will
  compile core from that directory instead of the embedded sources. The LSP
  uses the same override for core analysis, so go-to-definition for core
  symbols jumps into the override directory, and editing that directory works
  even when it is not literally named `core`. Go-to-definition now also
  follows resolved member accesses, including core methods reached through a
  protocol conformance such as `String.utf8()`. The LSP now handles the
  standard `shutdown`/`exit` lifecycle messages, so editor restarts can stop
  the running server cleanly. The VSCode extension now preserves the parent
  environment when spawning the LSP, exposes `talktalk.corePath` to pass
  `TALK_CORE_PATH` explicitly when VSCode's extension host does not inherit
  shell environment variables. `TalkTalk: Set Core Path` opens a folder
  picker and writes `talktalk.corePath`; `TalkTalk: Clear Core Path` removes
  it. Both commands offer to restart the language server.
  `scripts/reinstall-vscode-extension.sh` rebuilds the debug `talk` binary,
  packages the VSCode extension, and reinstalls it, including auto-detection
  of VSCode Remote SSH's remote CLI when `code` is not on `PATH`.
- **Member completion is less fragile while typing incomplete code.**
  Completion now keeps the dotted receiver when the dot appears in
  partially typed control-flow conditions, call and effect arguments,
  arrays, tuples, records, record spreads, match scrutinees, and match
  arm bodies. Parser recovery preserves those incomplete expressions long
  enough for the LSP to type the receiver, and borrowed core `String`
  completions still surface fields even when the member currently being
  typed does not resolve yet.

## Unreleased (2026-07-03) — Unicode characters

Strings now work in user-perceived characters. A `Character` is an
extended grapheme cluster (UAX #29, Unicode 17.0.0) — the Swift model —
so combining marks, emoji ZWJ sequences, flags, and Indic conjuncts each
count as one. The byte-level API didn't go away; it moved behind an
explicit view. Design and trade-offs:
docs/adr/0012-unicode-character-model.md.

### Characters

- **Strings iterate by character.** `String` and `Substring` are
  `Iterable` over `Character`, a borrowed view of one cluster's bytes —
  iteration allocates nothing. `count()` counts characters, documented
  O(n).

  ```talk
  print("héllo 👋🏽".count())      // 7
  print("👨‍👩‍👧‍👦".count())          // 1 — four scalars, three ZWJs, one character
  print("🇺🇳🇺🇳".count())           // 2 — four regional indicators, two flags

  for ch in "héllo" {
  	print(ch)                   // h é l l o, one per line
  }
  ```

- **No integer character indexing.** There is no `s[i]` and no
  `char_at`: nothing hides a linear scan or invites split characters.
  Positional work is iteration, `find`, and slicing at byte offsets you
  got from the API itself.
- **Ill-formed UTF-8 is safe to iterate.** Invalid bytes decode as
  U+FFFD error units (maximal subparts, §3.9.6 — the `from_utf8_lossy`
  policy) for classification only; each `Character` still views the raw
  bytes, so concatenating a string's characters reproduces it exactly.
- **Equality stays byte equality.** NFC `"é"` and NFD `"é"` compare
  unequal — canonical equivalence needs normalization tables talk does
  not carry. Documented at the top of `core/String.tlk`.

### The `utf8()` view

- **Byte access is explicit now.** `s.utf8()` returns a borrowed
  `UTF8View` with `count()`, `at(index)`, and `slice(start, byte_count)`
  — byte offsets, which may split characters; that is the point of
  asking for bytes. `byte_at`/`slice` are gone from `String` and
  `Substring`, and the `length` field is renamed `byte_count` so nothing
  character-shaped reads like a character count.

  ```talk
  let s = "café"
  print(s.count())           // 4
  print(s.utf8().count())    // 5
  ```

- **`find`/`find_from` return `Int?`** instead of a `-1` sentinel. The
  offset is a UTF-8 byte offset, valid as `utf8().slice` input
  (byte-wise search is exact for UTF-8: a needle only matches at
  character boundaries of itself).

### Self-hosted Unicode

- The UTF-8 decoder, the full UAX #29 break engine (GB3–GB999,
  including GB9c Indic conjuncts, GB11 emoji ZWJ sequences, GB12/13
  regional-indicator pairs), and the `Character` layer are all talk
  source (`core/Unicode.tlk`). The runtime still knows only bytes.
- Break categories live in a generated table (`core/UnicodeData.tlk`):
  a sorted boundary list packed into one 7-bit-clean string literal
  (~8.7 KB of interned static data, binary-searched in place).
  Regeneration is `cargo run --bin gen_unicode` over UCD files vendored
  in `dev/ucd/` — upgrading Unicode is a data refresh, reviewed as a
  diff.
- All 766 official GraphemeBreakTest-17.0.0 cases pass
  (`tests/unicode.rs`), alongside a semantic corpus run differentially
  on both engines.
- One compiler addition made the self-hosting possible: the `btoi` IR
  op (`Byte._toInt()`) — talk source previously couldn't do arithmetic
  on bytes.

### Fixed along the way

- **Invalid `\u{...}` escapes are hard errors.** Out-of-range and
  surrogate code points were silently dropped from string literals;
  they now fail at the lexer with a position, and lexer errors surface
  as real diagnostics instead of silently truncating the parse.
- **`let` shadowing works.** Blocks are now scopes in name resolution:
  same-named `let`s in sibling blocks are independent bindings and a
  nested `let` shadows the outer one. Previously every use in a
  function silently resolved to its last same-named declaration — a
  miscompile. Redeclaring a name within a single block is a resolution
  error for now (proper sequential rebinding is planned).
- **Expression-position `match` can deliver borrowed values.** The
  borrow checker now tracks provenance through a match's join, so
  returning a `Substring` chosen by a `match` works instead of
  reporting an unknown borrow.
- **Module exports carry only their own schemes.** A module re-exported
  every imported scheme under re-tagged symbol ids, letting a core
  symbol and a module-local symbol collide — stdlib member calls could
  resolve against unrelated core signatures depending on nothing more
  than symbol counts.

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
