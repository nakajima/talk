# Changelog

## Unreleased (2026-07-10) — Derived `Equatable`

Talk now automatically derives same-type `Equatable` conformance for value
structs and enums when every stored field or reachable enum payload also
conforms. Derived equality compares struct fields in declaration order and enum
tags before payloads, short-circuiting on the first mismatch. Generic and
recursive types are supported, and the protocol's default `notEquals`
implementation provides `!=` from the synthesized `equals` witness.

Explicit conformances continue to take precedence. Cross-type `Equatable`
applications and `'heap` structs are not derived automatically.

### Fixed

- **Patterns now view through borrows at every aggregate occurrence.** Tuple
  and record elements containing borrowed enums can use the same variant
  patterns as owned values; no owned/borrowed pattern syntax is required.
- **Exhaustiveness agrees with borrow-transparent pattern checking.** Valid
  nested borrowed variant patterns no longer produce cascading type errors or
  false unreachable-arm warnings.
- **Nested match ownership is tracked per projection.** Borrowed payload
  binders remain aliases while owned payloads in the same aggregate still
  receive their normal wildcard and scope-exit drops.
- **Type mismatch diagnostics now explain both sides.** Errors identify the
  relevant context, such as an annotation, function argument, assignment,
  return value, branch, condition, pattern, or array element, and state why
  the required type differs from the type that was found.

## Unreleased (2026-07-09) — Neotest and machine-readable test output

`talk test` now supports `--json` for machine-readable results. The JSON report
includes suite status, failure count, captured program output, and one record per
executed test with its name, status, and assertion failures. Compile, runtime,
discovery, and no-test outcomes also render as JSON when requested.

`talk test --filter NAME` runs only tests whose registered name exactly matches
`NAME`, for both human and JSON reporters. The filter is applied by the harness
while tests register, so skipped tests are not executed.

The Neovim runtime now includes a `neotest-talk` adapter. It discovers
`*.test.tlk` files, maps `test "name" { ... }` and `test("name") { ... }`
positions into Neotest, runs files via `talk test --json`, and uses
`--filter NAME` for single-test runs. Explicit package test paths may be
outside `tests/`, while pathless package test discovery still defaults there.
`talk setup nvim` installs the adapter alongside the existing filetype, syntax,
indent, and ftplugin files.

## Unreleased (2026-07-09) — Packages and `talk new`

Talk now supports directory-based source packages declared by `package.tlk`.
Packages can expose one library and one or more binary targets, and dependencies
compile as external modules rather than being flattened into consumer source.

Dependencies support pinned Git revisions, SHA-256-verified tarballs, and local
relative `.path` sources. `talk install` resolves the full graph into a checked-in
`package.lock`; `talk update` refreshes it; and `talk run`, `talk build`, and
`talk test` use the locked graph. Remote sources are cached by content identity,
while path dependencies remain mutable local development inputs.

`talk new <name>` creates a runnable binary package with `package.tlk`,
`package.lock`, `src/main.tlk`, and `tests/<name>.test.tlk`. Package manifests
are type-checked through `stdlib/Package.tlk`, so the LSP recognizes manifest
constructors and reports normal semantic diagnostics rather than an undefined
`Package` name.

## Unreleased (2026-07-09) — Labeled enum payloads

Enum cases can now label their fixed positional payloads:

```talk
enum Foo {
	case bar(fizz: Int, buzz: String)
}

let foo = Foo.bar(fizz: 123, buzz: "sup")
match foo {
	.bar(fizz: _, buzz: value) -> value
}
```

Labels are enum-case metadata rather than record-row fields. They are checked
at construction and pattern sites, must match declaration order, and lower to
the existing positional enum payload representation.

## Unreleased (2026-07-09) — Array.swap and typed raw-memory swap

`Array` now has `swap(i, j)`, implemented with copy-on-write uniqueness and a
new typed raw-memory swap primitive instead of value-level load/store traffic.
This gives sorting, partitioning, and shuffle-style code a direct in-place swap
path while preserving Array value semantics.

Inline IR gained `swap T ptrA ptrB`, lowered through lambda-G as `Op::Swap(T)`
and scheduled to a VM `Swap` bytecode instruction. The evaluator and runtime VM
swap the typed memory slot directly: byte elements swap one byte, while scalar,
pointer, and boxed aggregate elements swap their word/handle representation.
Core exposes this as `_swap<Element>(a, b)` in `Memory.tlk`, which
`Array.swap` uses after `uniqued_storage()`.

## Unreleased (2026-07-08) — Protocol-head conformance axioms (ADR 0020)

Protocol-head conformance extensions are now first-class conformance axiom
schemes. An extension such as:

```talk
extend Iterator: Into<Array<Element>> {
	consuming func into() -> Array<Element> { ... }
}
```

means `forall Self. Self: Iterator => Self: Into<Array<Self.Element>>`,
rather than a nominal conformance for a type literally named `Iterator`.
Default-only `extend P { ... }` still registers protocol extension methods as
requirements, while `extend P: Q { ... }` now goes through the same conformance
row machinery as other conformances.

The collector binds a protocol head's `Self`, protocol parameters, and declared
associated types as row parameters. The solver can now satisfy non-nominal
`Conforms` wanteds by matching protocol-head axiom conclusions, substituting
premises, and carrying the selected witness/member instantiation into the typed
output. Member lookup dispatches through these axioms for concrete, generic,
existential, and projection receivers, and the published instantiations carry
protocol `Self`, protocol arguments, and associated projections to lowering.
Existential associated-type overrides now normalize through projection reads.

Overlapping candidates are reported as overlapping conformances instead of
choosing the first table row. Recursive conformance applications now produce a
`Recursive protocol conformance` diagnostic rather than looping until overflow,
and the solver has a hard step limit with rendered constraint summaries as a
last-resort guard.

## Unreleased (2026-07-08) — First-class iteration and access-marked for loops (ADR 0021)

`for` loops are no longer erased by a pre-resolution syntactic desugar. The
parser and resolver keep `StmtKind::For` as a real source construct, including
its iterable access marker:

```talk
for item in items { ... }          // shared, calls iter()
for item in mut items { ... }      // exclusive, calls iter_mut()
for item in consume items { ... }  // consuming, calls into_iter()
```

The type checker resolves the implicit `iter`/`iter_mut`/`into_iter`, `next`,
and mut-mode `write_back`/`finish` calls on checker-minted node ids and
publishes a `ForPlan`. Typed-program building then elaborates the checked loop
into ordinary typed nodes at those ids, so flow and lowering see real calls with
normal member resolutions, instantiations, effects, drops, and ownership facts.
The loop binder's type comes from the selected iterator's `Element` through the
`.some` payload of `next()`, not from a synthetic pre-check declaration.

Mut iteration moves the source into an iterator, writes a single-name binder
back after each completed iteration, and restores the source with `finish()` at
loop exit; unsupported markers, non-variable mut sources, and mut destructuring
are diagnosed. Flow/lowering learned the resulting loop, borrow, write-back,
and body-value drop shapes instead of rediscovering them from resolver-made
source.

Core iteration was reshaped around this model. `Iterator` now provides default
`iter()`/`into_iter()`, consuming `map`/`skip`, `index`, and `to_array()`, plus a
blanket `Into<Array<Element>>` conformance through the protocol-head axiom
scheme. `Array` has borrowed `iter()`, consuming `into_iter()`, mut
`iter_mut()` with `write_back`/`finish`, and `_replace` for write-back. The
`From` and `Into` protocols now use protocol inputs (`From<Source>`,
`Into<Target>`) instead of associated outputs.

## Unreleased (2026-07-08) — Character literals and syntax sugar (ADR 0022)

Single-quoted character literals now have their own token and expression form:
`'a'`, `'😎'`, `'\n'`, and `'\''` type as `Character`. The lexer distinguishes
them from effect names/effect rows, validates literal escapes and Unicode
escapes, and reports empty or invalid character literals. Formatting,
highlighting, typed-AST construction, checking, and lowering now preserve them;
lowering builds a `Character` value over interned literal bytes using the same
unescape path as string literals.

Several small call/closure sugars also landed:

- calls may omit parentheses when the first argument is a string literal:
  `say "hello"` and `say "hello" { ... }`;
- a parenthesized final block argument is treated as the trailing block:
  `map({ x in x })` parses like `map { x in x }`;
- trailing closure blocks can synthesize positional block parameters from
  `$0`, `$1`, ... usages, so `map { $0 * $1 }` works without an explicit
  argument list.

## Unreleased (2026-07-07) — Borrow-by-default parameters (ADR 0018)

Function parameters are now borrow-by-default. An unadorned `x: T`
parameter is a shared borrow; ownership modes are spelled on the
parameter instead of in its type:

- `func read(x: Foo)` — shared borrow (the quiet default)
- `func update(mut x: Foo)` — exclusive/inout borrow with caller
  write-back (works for method receivers and a free function's first
  parameter)
- `func store(consume x: Foo)` — the callee takes ownership (the old
  meaning of `x: Foo`)
- `init` parameters (including synthesized memberwise inits) and effect
  operation parameters still consume by default; `borrow x: T` opts an
  init parameter out.

Function TYPE parameters follow the same spelling: `(Foo) -> Void`
borrows, `(mut Foo) -> Void` is exclusive, `(consume Foo) -> Void` is
owned. Call sites gained explicit ownership markers — `f(consume x)`
forces a move (disabling automatic cloning), `f(copy x)` forces an O(1)
clone, `f(borrow x)`/`f(mut x)` assert the parameter's mode.

Shared borrows of Copy-grade types erase at elaboration (`&Int` never
surfaces), extending ADR 0014. Value-semantic (CheapClone) arguments
still coerce borrowed→owned with an inserted retain; generic `T` does
not implicitly clone, so identity-style functions now spell
`consume x: T`. Rvalue aggregates passed as call operands get structural
temporaries so borrowed callees leave the caller a drop point.

Core and the stdlib migrated to the new spelling; the formatter prints
it (and canonicalizes legacy `&` in function-type positions). Legacy
`&T`/`&mut T` parameter annotations remain accepted. `mut` parameters
beyond the single v1 write-back slot, `mut` parameters on function
values, and temporaries passed to `mut` are rejected with diagnostics
instead of silently dropping mutations.

## Unreleased (2026-07-06) — Effectful function type annotations

Function type annotations now carry explicit effect rows. Syntax such as
`() 'io -> Int`, `() '[read, write] -> Void`, and `() '[] -> Void`
parses into `TypeAnnotationKind::Func { effects, .. }` instead of
silently creating an inferred open row. The checker lowers those effect
sets into the function type's latent effect row, so annotated closure
values and higher-order parameters can bound or close the effects they
permit.

Name resolution, formatting, highlighting, goto-definition, and rename
coverage were updated for effects that appear inside function type
annotations.

## Unreleased (2026-07-05) — Heavily WIP C/iOS embedding facade

A new `talk-c` workspace crate exposes a heavily WIP C ABI facade for
embedding Talk in Swift/iOS and other C-compatible hosts. The facade
wraps the compiler pipeline, bytecode compilation, formatting,
highlighting, direct workspace language-service APIs, and REPL support
behind opaque handles instead of exposing Rust internals directly.

Language-service calls now use typed C result handles rather than JSON:
diagnostics, hover, completions, ownership inlay hints, highlight
tokens, goto definition, rename edits, evaluation results, and REPL
completions are all read through count/get/value accessors. Returned
strings are borrowed `TalkStringRef` slices tied to the result handle's
lifetime, so host wrappers should copy them before freeing the handle.
Raw string/byte APIs still use `TalkResult` for formatting, HTML
highlighting, IR/bytecode rendering, and bytecode emission. The embedded
facade now reports panic payloads instead of only `talk-c: internal
panic`, making release-build failures easier to diagnose from Swift.

Core and stdlib caches now use retryable `OnceLock` initialization instead
of poisonable `lazy_static` cells. A failed embedded initialization no
longer permanently poisons the process and turns every later call into a
secondary `Once instance has previously been poisoned` panic. Bundled
stdlib sources are also materialized into a runtime temp directory when
the build-machine source path is not present, so relative stdlib imports
such as `testing.tlk` importing `ansi.tlk` work from XCFramework builds.

The analysis layer gained protocol-independent goto-definition and rename
entry points so embedders can call the language-service functionality
directly without running the LSP server. The TalkSwift release workflow now
listens to tag push, tag create, and GitHub Release published events for
non-`-swift` tags, and also has a manual fallback that accepts a base tag:
it builds `TalkC.xcframework.zip`,
computes the SwiftPM checksum, stamps the root package manifest, creates a
derived `<tag>-swift` tag, and uploads the XCFramework zip as a GitHub
Release asset for that Swift tag.

A heavily WIP `talk-swift` Swift package now wraps the local `talk-c`
facade. The repository root now also has a SwiftPM `Package.swift` for
remote Xcode/SwiftPM consumption from version tags produced by the
TalkSwift XCFramework release workflow. The local nested package can
consume a generated `TalkC.xcframework` when present or fall back to a
system-library import of `talk_c.h` plus a caller-provided `libtalk_c`
linker search path. The Swift layer copies borrowed C string slices into
native Swift values and exposes typed wrappers for workspace, compiler,
highlighter, and REPL operations.

This interface is intentionally not stable yet: naming, result shapes,
threading expectations, Swift package layout, and XCFramework packaging
are still expected to change.

## Unreleased (2026-07-05) — LSP rename coverage

LSP rename now covers the symbol surfaces that have first-class source
names: fields and member accesses, struct constructor argument labels,
methods, enum variants in constructors and patterns, effects in
declarations/effect rows/handlers/performs, and associated type bindings
and projections. Initializers remain intentionally non-renamable because
`init` is syntax, not an independently named symbol.

Regression coverage was added for property, method, effect, variant,
associated-type, and core-source renames. Core source symbols such as
`core/File.tlk`'s `File` are now considered local to a Core workspace,
so they can be renamed while editing Core itself without enabling rename
of imported Core symbols from ordinary workspaces.

## Unreleased (2026-07-05) — Drop correctness and protocol-argument fixes

Structural temporary drops now replace the MIR builder's ambient
`pending_temp_drops` accumulator. Temporaries are recorded by the
statement that creates them and their `TemporaryEnd` drop candidates are
emitted at that statement's completion point. This fixes a double-free
where a call argument temporary could be dropped from inside a trailing
closure body and therefore freed once per callback invocation.

Protocol-argument conformance handling also received correctness fixes:

- Super-protocol traversal is bounded by protocol symbol, preventing
  argument-growing recursive protocol graphs from hanging the checker.
- Bound-based conformance solving no longer commits to the first
  protocol+arity match when multiple protocol applications are in scope.
- Existential protocol annotations validate protocol arity again.
- Associated-type generic arity for protocol bounds counts only directly
  declared associated types, not inherited ones.
- Member/evidence lookup paths preserve full protocol applications where
  needed, including parameterized conformances.
- Protocol member dispatch deduplicates inherited candidates by
  requirement symbol and reuses `ProtocolApplication::substitution`.

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
