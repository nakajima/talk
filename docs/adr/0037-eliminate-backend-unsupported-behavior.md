# 0037 - Eliminate backend capability rejections

Status: proposed

## Context

The bytecode backend restored broad source and tool parity behind the deep
`compile`/`execute` interface adopted by ADR 0034. It still contains 65 calls
to `BackendError::unsupported`. They cover a mixture of real capability gaps,
duplicate guards for one gap, conservative restrictions, malformed states that
should have been rejected by the frontend, and catch-all branches whose source
reachability is unknown.

This creates an unstable language contract. A program can parse, resolve, and
type-check successfully, then fail only when MIR construction happens to visit
one of these branches. The failures are also demand-sensitive: an unused
function may appear valid until check-all mode compiles it, a generic body may
fail only at one instantiation, and an editor cannot tell whether accepted
source is executable without invoking the backend.

The motivating example is an ordinary method receiver captured by a trailing
block:

```talk
self.peek().map { ch in
    self.char_at(self.current + ch.utf8_count())
}?
```

The frontend accepts the closure and the backend already represents closure
environments, but MIR construction does not give the implicit receiver a safe
owning capture. It eventually reports `function and global values are not
supported yet`. Rewriting the source as a `match` avoids the backend path but
does not resolve the missing behavior.

The unsupported sites are not one feature. They fall into these capability
families:

- places, initialization, assignment, and `mut` writeback;
- generic ownership witnesses and conformance dictionaries;
- owning, borrowed, mutable, recursive, and generic closure captures;
- destructuring, open-row, string, generic, and existential patterns;
- general globals, linear globals, and external callable supply;
- derived `Showable` and equality operations;
- user handling of ambient core effects;
- trusted inline IR operations, operands, and type annotations; and
- generic fallback branches for declarations, expressions, constructions,
  values, and patterns.

Leaving those families as unrelated fail-closed branches is cheaper locally but
keeps backend completeness unknowable. Moving the same branches into an editor
preflight pass would improve timing while preserving the capability gaps and
would create a second owner for backend support.

## Decision

Every valid, well-typed Talk program has an executable meaning in the reference
bytecode backend. The backend may not reject such a program merely because a
source form, type shape, ownership operation, generic boundary, or runtime
representation has not been implemented.

The implementation will eliminate every current
`BackendError::unsupported` site. Each site must end in exactly one of three
states:

1. the source behavior executes through the bytecode backend;
2. the source is semantically invalid and the owning frontend or MIR analysis
   reports a structured language diagnostic; or
3. an external implementation is required and the linker reports a structured
   missing-supplier diagnostic.

The second and third states are not backend capability rejections. They express
stable language or linking rules. Recovery-only typed-tree forms and violated
compiler invariants become internal compiler errors and are never rendered as
ordinary source diagnostics.

Completion requires:

```text
rg "BackendError::unsupported" src/backend
```

to return no matches.

This decision preserves ADR 0034's one deep backend interface. MIR,
monomorphization, glue generation, and bytecode details remain private. The
work deepens the existing backend module rather than publishing new phase
artifacts or introducing a second evaluator.

## Admission rule

The initial implementation step is an executable inventory, not a refactor.
Every unsupported call site receives a minimal source fixture and one
classification:

- valid behavior;
- duplicate guard for a valid behavior;
- frontend-invalid source;
- linker failure;
- recovery-only or internal invariant.

The inventory groups duplicate guards by capability family and records the
expected final behavior. A repository test prevents adding a new unclassified
unsupported site while the migration is in progress.

A catch-all branch is not assumed unreachable. It must have a test proving the
frontend erases or rejects the form before the branch can become an internal
invariant.

## 1. Places and initialization

MIR will use one private place representation for writable storage:

```text
Place
  root: local | global | capture | temporary
  projections: field | tuple element | record field | payload
```

The place interface owns these operations:

```text
load
initialize
replace
move/take
borrow shared
borrow mutable
```

This replaces syntax-specific assignment and writeback branches. It supports:

- `let` declarations without initializers;
- definite-assignment checking before every read;
- assignment to globals, captures, and nested projections;
- replacement with exactly-once destruction of the old value;
- `mut` arguments and requirements over any writable place; and
- temporary materialization for a `mut` rvalue whose evolved value is
  discarded.

Uninitialized storage has no default value. MIR dataflow tracks its state and
reports a source diagnostic when a path can read it before initialization.
Storage initialization and ownership liveness are one analysis over the same
place identities, not parallel syntax walks.

## 2. Universal value operations and generic evidence

The backend will have one private authority for operations on a resolved runtime
value type:

```text
retain
destroy
equality
show
selected conformance requirements
```

Concrete types receive generated operations. A rigid generic type receives the
same operations in a witness bundle. The bundle is threaded consistently
through direct generic calls, indirect calls, closure environments,
existential packages, generic effects, imported generic implementations, and
generated glue.

The frontend remains the authority for conformance selection. The backend
transports and invokes the selected evidence; it does not repeat conformance
search.

This mechanism must handle nested rigid positions such as
`Array<(Int, T)>`, not only a payload whose complete type is `T`. It replaces
all branches reporting absent ownership witnesses, absent conformance
dictionaries, compound rigid evidence, unresolved generic effect
instantiations, unsupported value types, and existential requirements without a
runtime implementation.

Derived equality and `show` use the same value operations. They cover every
type shape for which the frontend publishes the corresponding conformance,
including tuples, closed records, structs, enums, existentials, and generic
values. The frontend must not publish structural conformance for a shape whose
operation has no language semantics, such as function equality.

## 3. Owning closure environments

Closure environments become type-aware owning values. Each environment records
its capture slots, capture modes, value operations, inherited generic evidence,
and captured effect capabilities.

The backend will support:

- implicit method-receiver capture;
- Copy and implicit-sharing snapshot captures;
- consuming captures;
- shared and mutable borrow captures;
- ownership-sensitive mutable cells;
- recursive closures and mutually recursive local functions;
- generic local functions that capture; and
- named functions with explicit capture lists.

Capturing a shareable managed value retains a snapshot according to the
implicit-sharing decision in `docs/ownership-rethink-plan.md`. Capturing a
strict-linear value still obeys linear consumption and cannot be silently
copied. A consuming capture moves it. A stored borrowed capture must either be
proven not to escape or be promoted to the owning stored-view representation
required by the same implicit-sharing decision.

Closure copy and destruction use generated environment retain/drop glue. The
last closure reference releases every owning capture exactly once, including on
early returned and discontinued paths. Generic capture slots carry the witness
bundle required to perform that cleanup. Cells and recursive environments are
covered by the same lifecycle rather than exempted from resource accounting.

This section removes all capture-related unsupported branches and directly
covers the motivating `self` capture.

## 4. Patterns and dynamic projection

The pattern compiler will account explicitly for every payload on every arm. A
payload is moved to a binder, borrowed, retained/copied, or destroyed because
it is unbound. The outer aggregate is never a second implicit owner after its
payloads have been extracted.

The implementation covers:

- every typed destructuring form;
- or-patterns whose alternatives leave different owned payloads unbound;
- record patterns that bind a field and inspect its interior;
- open-row record patterns;
- string patterns through checked equality;
- positional members on generic and existential values; and
- generic tuple, record, and nominal projections.

Closed and monomorphized rows use static slots. A genuinely open runtime row
carries a row-layout dictionary mapping labels to slots. Generic and
existential positional projection uses layout or witness evidence rather than
reconstructing a concrete type.

A consuming pattern that binds both a whole owning field and an interior value
must make the ownership relation explicit: the interior is borrowed from the
whole, copied when evidence permits, or retained as a snapshot. Two binders do
not independently claim the same ownership reference.

## 5. Globals and external implementations

Every global has stable storage, an initializer thunk, initialization state,
move state, type-aware teardown, and deterministic module ordering. Literal
shape no longer determines whether a global is executable.

The backend supports aggregate globals, non-literal initializers,
function-valued globals, global closures, general global reads, and replacement
where the declaration permits mutation.

Strict-linear globals use whole-program finite-exit analysis. Callable summaries
record each global initialization, read, move, reinitialization, and
consumption. Summaries are solved to a fixed point over the reachable call
graph, including the finite target sets of indirect calls. A valid entry must
consume each live linear global exactly once on every finite exit. A program
that cannot satisfy that rule receives the same linearity diagnostic as an
invalid local program; linear globals are no longer rejected as a class.

Every callable reference resolves to exactly one supplier:

- a source body in the compiled graph;
- a linked bytecode implementation;
- a declared host function; or
- a trusted intrinsic.

Separately compiled modules use stable symbol identity and a validated callable
interface. A declaration for which no supplier exists is a linker error, not an
unsupported source form.

## 6. Ambient core effects

The runtime's host implementation becomes the outermost fallback handler for
ambient core effects rather than an unconditional bypass of the user handler
stack. A nearer user handler can intercept a core effect, resume or discontinue,
and delegate by performing outward to the host fallback.

This applies to typed core operations such as IO and async requests. Trusted
allocator and raw-memory primitives remain unhandleable unsafe intrinsics. If a
current core effect conflates a typed request with allocator integrity, it must
be split before user interception is enabled.

Handler routing, cleanup, resource ownership, and one-shot continuation rules
remain those of ADRs 0011, 0027, and 0032. Tests must cover nested user/core
handlers, host fallback, resume, discontinue, and cleanup when a handler
substitutes a result.

This supersedes the parity-ledger and rebuild-plan restriction reserving all
ambient core effects exclusively for the runtime.

## 7. Trusted inline IR

Every parser-admitted trusted inline IR instruction receives either a complete
implementation or a frontend type error for an invalid operation/type
combination. Backend lowering is exhaustive over instruction and operand
variants.

The implemented instruction families include arithmetic, comparison, bitwise
operations, allocation, load, take, store, free, retain, memory copy, swap,
pointer arithmetic, inline array access, host IO, conversions, and uniqueness
checks.

Inline IR type annotations use the same runtime type and value-operation
machinery as ordinary source. They are not restricted to the scalar helper.
Operands include registers, bound expressions, scalar constants, records, raw
pointers, static raw buffers, `uninit`, and `poison`. `uninit` and `poison` have
validated trap semantics and may not become ordinary source values.

The existing unsafe gate remains mandatory. Supporting trusted inline IR does
not make raw operations safe or remove bytecode validation at the serialized
module trust seam.

## 8. Exhaustive backend lowering

After the preceding mechanisms land, the remaining generic fallbacks for
unsupported declarations, expressions, patterns, constructions, fields, and
value types are audited against the typed-tree enums.

For every variant, the final state is one of:

- exhaustively lowered;
- erased by a documented frontend transformation;
- rejected by the frontend with a structured diagnostic; or
- recovery-only and asserted unreachable in compilation.

Generic unsupported messages are not retained as defense in depth. A violated
construction invariant is an internal compiler error with enough context to
debug the producer.

## Implementation order

The work lands in dependency order:

```text
0. executable inventory
1. places and initialization
2. universal value operations and generic evidence
3. owning closure environments
4. patterns and dynamic projection
5. globals and external implementations
6. ambient core effects
7. trusted inline IR
8. exhaustive fallback removal
```

Places and value operations are the shared foundation. Closure environments,
patterns, and globals must not each invent their own projection, retain, or
drop conventions. Ambient handlers wait for closure and generic-environment
layout to stabilize. Inline IR reuses place and value semantics rather than
building a parallel memory model.

Each wave is driven by the inventory fixtures for that family and removes the
corresponding unsupported sites in the same change. A wave may not replace one
unsupported branch with another broader fallback.

## Validation

Every implemented family requires black-box tests through the public backend
interface. Tests cover, where applicable:

- `talk check` acceptance and `talk run` execution;
- concrete and generic values;
- direct and indirect calls;
- local, captured, global, and imported storage;
- normal return, early return, loop exit, handler resume, and discontinue;
- exact allocation, object, cell, closure-environment, and host-resource
  balance;
- no duplicate destruction or use after move;
- source modules and linked module suppliers; and
- bytecode encode, decode, validation, and execution for new target forms.

The existing parity programs, Core and stdlib suites, `talk-syntax`, package
execution, REPL, C/Swift embedding, and browser embedding remain required
regression surfaces.

The final gate additionally requires:

1. every initial unsupported site has a reviewed disposition and fixture;
2. no `BackendError::unsupported` constructor or call remains;
3. the typed declaration, expression, pattern, inline-IR instruction, and
   inline-IR operand enums are exhaustively accounted for;
4. malformed source fails before backend construction;
5. missing external supply fails at linking; and
6. all resource-balance fences pass.

## Relationship to earlier decisions

This ADR preserves ADR 0034's one deep backend interface, private phases, trust
policy, bytecode reference target, and prohibition on a second evaluator. It
extends ADR 0034's parity goal from the frozen required corpus to all valid
frontend-accepted behavior.

It preserves the semantic authority of ADR 0032 for ownership, deterministic
cleanup, generic evidence selection, and one-shot effects. Its implementation
uses the later implicit-sharing decision in `docs/ownership-rethink-plan.md`
for managed captures and snapshots.

It supersedes only the blanket implementation restrictions recorded in the
backend parity ledger and lean rebuild reports: owned captures, generic
capturing local functions, linear globals as a class, uninitialized bindings as
a class, and user handling of all ambient core effects. Invalid instances of
those behaviors remain ordinary ownership, initialization, unsafe, or linking
errors.

ADR 0034's size accounting remains mandatory. Its 13,400-line threshold is an
architecture-review trigger, not permission to retain unsupported behavior.
Crossing it requires reviewing whether the new implementation has duplicated
places, value operations, dictionaries, or lifecycle rules before widening the
budget.

## Consequences

- Backend completeness becomes an invariant rather than a ledger of exceptions.
- Several currently separate branches deepen into shared place, value-operation,
  closure-environment, and pattern mechanisms.
- The implementation is substantially larger than moving backend errors into
  editor diagnostics, but it removes the rejected behavior instead of changing
  when users discover it.
- Linear globals, ambient core handlers, open rows, owning stored views, and
  precompiled callable supply require real semantic and runtime work; they are
  not hidden behind syntax-specific exceptions.
- Some failures move earlier because they are language-invalid, but no valid
  typed program fails for lack of backend support.
- New source features must extend the backend in the same change or define a
  frontend rejection. Adding another open-ended backend capability rejection is
  contrary to this decision.
