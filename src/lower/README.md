# How the lowerer works

This directory translates typed Talk into lambda-G. Its inputs are
`LowerUnit`s: a `TypedProgram` view (`src/compiling/typed_program.rs`) and
the checked MIR store built by `mir::build_checked` in `src/lower/mir.rs`.
The driver supplies units for Core, bundled stdlib modules, and the user
program; generic library code is specialized on demand together with the
program that uses it.

The detailed source-level `@_ir`, printed lambda-G, and `talk ir`
bytecode formats are documented in
`../../docs/ir-and-lambda-g-format.md`. What comes out is a fully
monomorphic, continuation-passing lambda-G program plus the set of labels
that the VM scheduler must keep as chunks. Effect rows are erased as
static types, but user effects whose rows survive into a function become
explicit capability parameters.

Main files:

- `mod.rs` — orchestration, expression lowering, context state, and
  `lower_program`.
- `demand.rs`, `functions.rs`, `theta.rs` — indexing lowerable bodies,
  monomorphization, function calling conventions, and type substitution.
- `mir.rs`, `mir_lowering.rs`, `statements.rs` — checked MIR construction and
  the lowering of blocks, statements, control flow, drops, and temporaries.
- `calls.rs`, `values.rs`, `closures.rs` — calls/member dispatch,
  construction/projection/storage, and function values/closures.
- `patterns.rs`, `matches.rs` — match decision trees, GADT evidence, and
  existential packing around matches.
- `effects.rs` — lexical effect handlers and capability passing.
- `derive.rs` — synthesized `Showable` witnesses.
- `splices.rs` — source-level `@_ir` instructions to lambda-G primops.

## Continuation-passing: the calling convention

lambda-G functions never return, so every Talk function lowers to a
lambda-G function with one extra parameter: the continuation to call with
its result. Written as pseudocode:

```talk
// what you wrote
func add(a, b) { a + b }

// the shape the lowerer produces
func add(a, b, k) { k(a + b) }
```

Sequencing materializes continuations. To lower `f(g(x))`, the lowerer
makes a small function to receive `g`'s result, then runs `g` first:

```talk
func after_g(result) { f(result, k) }
g(x, after_g)
```

The MIR lowering path does this for statements, argument evaluation,
branches, loops, matches, handlers, and drops. Pure expressions that can
be emitted directly (variables, literals, arithmetic on pure operands,
field extraction from already available values, etc.) avoid creating an
extra continuation.

`return` is a call to the function's return continuation. Loops become
continuations/blocks that jump back to themselves; `break` and `continue`
call the continuations recorded for the enclosing loop. Match arms, `if`
branches, and other joins deliver their value to a shared join
continuation.

## Monomorphization and dispatch

The lowerer never emits a generic function body. `demand(symbol, theta)`
returns the label for one concrete specialization, creating a stub and
queueing the body the first time that `(symbol, theta)` pair is needed. A
worklist drains until no demanded specializations remain. The `theta` map
comes from the checker's per-call-site instantiation table composed with
the containing specialization's `theta`, so generic code calling generic
code bottoms out in concrete types without runtime type tags.

Member calls use the checker's `member_resolutions` when they are already
committed to a direct member or conformance witness. If a member constraint
rode a qualified scheme and was intentionally left unresolved until a call
site, the lowerer re-resolves the label against the now-concrete receiver:
inherent struct/enum/extend members first, then protocol witnesses and
defaults, then derived `Showable` when applicable. Owner type arguments
are recovered from the concrete receiver (`owner_theta`), so methods of
generic structs and inherent extensions specialize correctly.

Function values and escaping continuations become real VM chunks with flat
closure environments. Named local functions are labeled before bodies
lower, so local recursion and mutual recursion work independently of
source order.

## Data representation

- Scalars (`Int`, `Float`, `Bool`, `Byte`, `RawPtr`, `Void`, `Never`) map
  to lambda-G scalar/bottom types.
- Anonymous records are tuples. Field labels are sorted into a canonical
  order; `r.a` is an extract at the statically known position for the
  current specialization. Assigning through a record path rebuilds the
  tuple along that path.
- Ordinary structs, strings, arrays, and other value aggregates are boxed
  records (`RecordNew`, `GetField`, `SetField`). `SetField` is a
  functional update; value semantics are preserved.
- Structs declared with the `'heap` attribute lower to region-managed
  objects (`ObjectNew`, `ObjectGet`, `ObjectSet`, `RegionAcquire`,
  `RegionRelease`) with finalizer thunks for `Deinit`/field teardown.
- Enums are tagged variants (`VariantNew`, `GetTag`, `GetPayload`). GADT
  constructor-local evidence is stored as runtime witness tables when a
  hidden payload may later be packed into an existential.
- Protocol existentials (`any P<...>`) are payload-plus-witness-table
  packages. The checker records implicit pack sites; lowering builds the
  payload package, witness wrappers, associated evidence layout, and the
  drop witness carried in the last slot.
- Mutable bindings are cells (`CellNew`, `CellGet`, `CellSet`). Assigned
  locals/parameters and mutating-method receivers are assignment-converted;
  mutable top-level bindings are registered in `top_level_cells` so
  functions capture main's cell rather than using global-variable machinery.
- `mut func` on value receivers uses an inout convention: the continuation
  receives `[result, new_self]`, and the caller writes the new self back to
  the receiver place. `'heap` receivers mutate in place and do not use the
  pair convention.

## Effects and handlers

Core effects (the runtime-supported io/alloc/async surface) lower
directly to runtime primops and do not become capabilities.
User-declared effects are capability-passing CPS:

- A function specialization whose latent effect row contains a user effect
  gets one extra capability parameter per concrete `(effect, type-args)`
  occurrence, placed before the return continuation.
- `@handle 'effect { ... }` installs a handler template in the lexical
  context. When a perform needs a concrete instantiation, the lowerer
  materializes a capability closure from the nearest template and memoizes
  it.
- A perform with a capability in scope calls that capability with the
  payloads and a resumption continuation. For a `Never`-returning effect,
  the resumption is a deliberately bodyless trap continuation because the
  checker rejects `continue` there.
- A handler that resumes calls the resumption. A handler that aborts
  finishes into the delimiter captured when the handler was installed, so
  code between the perform and the handler scope simply does not resume.
- Taking an effectful function as a value eta-expands it into a plain
  closure that captures the capabilities available at that point.

Unsupported handler/perform shapes emit lowering diagnostics and lower to
bodyless trap functions so reaching them fails loudly.

## Pattern matching (`patterns.rs`, `matches.rs`)

Matches compile to decision trees. The compiler works over a pattern
matrix: choose a column that tests something, split enum columns with a
switch on the tag, compile literal columns as equality chains, destructure
tuples/records/structs in place, and duplicate rows for or-patterns. Each
source arm's body is lowered once into a function taking that arm's
bindings (and any GADT evidence tables); multiple switch cases reaching
the same arm call the same function, which is the CPS rendering of a join
point.

## Derived show (`derive.rs`)

When the checker discharged `Showable` structurally (no explicit
conformance), there is no witness body to demand. The lowerer synthesizes
one directly in lambda-G: a chain of string-literal and sub-`show` calls
folded through the `String: Add` witness, printing
`Name(field: value)` for structs and `Name.variant(payloads)` for enums.
Recursive types work because the synthesized witness is itself demanded
through the normal `(symbol, theta)` cache.

## Further reading

CPS with continuations as ordinary functions and primitives in direct style
is the Thorin arrangement (Leißa, Köster & Hack, CGO 2015); the translation
is a first-order rendering of Danvy & Filinski, *Representing Control*
(1992). Lazy `(symbol, theta)` specialization is MLton's whole-program
model and rustc's monomorphization collector; witness-direct protocol
dispatch follows Jones (PEPM 1994). Capability-passing effects follow the
same family as Schuster, Brachthäuser et al. (PLDI 2022). Pattern
compilation follows Maranget, *Compiling Pattern Matching to Good Decision
Trees* (ML 2008), with join points per Maurer, Downen, Ariola & Peyton
Jones (PLDI 2017). Derived instances as compiler-supplied class defaults
go back to Wadler & Blott (POPL 1989).
