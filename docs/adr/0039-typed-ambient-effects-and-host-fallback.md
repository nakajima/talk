# 0039 - Host fallback handlers in core source

Status: accepted; implemented (2026-07-23) — see Implementation notes

## Context

Talk has dynamic, deep, one-shot effect handlers. User effects route through
the ordinary handler stack:

```text
perform
  -> find the nearest live handler
  -> invoke its clause outside its own search floor
  -> resume or discontinue
```

A clause delegates by performing the same effect again. Because its search
floor excludes itself, the new perform reaches the next outer handler.
Function values capture effect capabilities at their creation site, while a
perform without a captured capability searches the dynamic stack.

Core effects did not follow this path. The backend recognized `'io`
specially, dispatched its `IORequest` directly to the host instruction,
rejected user handlers over any effect declared by Core, and excluded all
Core effects from closure capability capture. The runtime therefore acted
as an unconditional bypass, not as an outer handler. That restriction
prevented useful handlers — deterministic test IO, logging, request
substitution, embedding-specific policies — and it made "declared by Core"
carry runtime policy, which is a fact about code ownership, not about
safety.

ADR 0037 requires valid checked effects to execute without backend
capability rejections. ADR 0038 requires effect legality and contracts to
be decided by typing rather than reconstructed by MIR.

## Decision

There is one effect-routing mechanism, and **the compiler special-cases no
effect anywhere**. The host's behavior is ordinary Talk source in
`core/Host.tlk`:

- `_io_host(request: IORequest) -> Int` — the host adapter, a 24-arm
  exhaustive match dispatching each request case through the generic
  inline-IR instruction `io <op> <a> <b> <c>` (op is an immediate indexing
  the runtime's operation table; unused slots pass zero). Adding a request
  case forces an arm here via exhaustiveness.
- `_with_host(consume body: () '[io, alloc, async] -> ()) -> ()` — installs
  the host fallbacks as three ordinary `@handle` statements (io delegates
  to `_io_host`; alloc and async resume immediately — allocation
  bookkeeping is carried by the `'unsafe` intrinsics, and the reference
  host has no scheduler), then calls the program.

The compiler knows exactly one well-known symbol: `_with_host`.

- **Entry assembly** wraps the program (script or named entry, including
  module initialization) in a call to `_with_host`, threading the program
  value through a hidden global slot since the callback returns unit.
  Programs without core run directly and have no ambient effects.
- **Typing** derives the ambient entry-row base from `_with_host`'s scheme:
  the effect row its callback parameter declares. Which effects are ambient
  is stated once, in core source, as an ordinary function signature.
- **MIR** treats every declared effect identically: performs use the
  capability path, closures capture capabilities for every declared effect
  in their row (a handler always exists at any legal capture point), and
  `@handle` is legal over any declared effect. Only the undeclared
  compile-time `'unsafe` capability stays outside the handler stack
  (`@unsafe` is its mask; the lexical gate is unchanged).

Routing order for a host effect is therefore the ordinary order:

```text
nearest user handler -> next outer user handler -> core's fallback clause
```

with delegation, substitution, resume, discontinue, unwind cleanup, and
function-value capture all the existing mechanisms. The fallbacks always
resume and never discontinue. They die with the wrapper frame like any
handler; global teardown runs outside them, which is sound because deinit
hooks are statically barred from performing effects.

## Interception safety for raw `'io`

The interception surface for `'io` is the raw `IORequest`. This is sound
under three guarantees:

1. **Pointers are inert in safe code.** A handler can hold or pass along a
   `RawPtr` from a request, but minting or dereferencing one requires the
   lexical `'unsafe` gate.
2. **The host adapter is defensive.** The runtime bounds-checks every
   pointer and length against VM memory before touching the host.
3. **Core wrappers clamp replies.** The performer-side trust points are the
   reply counts core uses to set view lengths. Each wrapper clamps the
   count to the capacity it actually allocated (`_io_clamp` in
   core/IO.tlk), so a lying handler yields wrong data, never an
   out-of-bounds view. Wrong data is precisely what interception is for.

Handlers written against the raw request shape will break if a nicer typed
request API replaces it later; that is an accepted pre-1.0 cost, not a
soundness prerequisite.

`print` and `write_string` do not perform `'io` — they lower through the
raw `io` instruction directly — so they remain uninterceptable until core
routes them through the effect. That is a separate decision because it
adds `'io` to many inferred rows.

## Alternatives rejected

### Keep the unconditional runtime bypass

Prevents user interception, leaves valid checked handlers rejected by MIR,
and retains two effect-routing models.

### Make `FindHandler` perform a magical host call on a miss

Moves source-effect ABI knowledge into the runtime and creates a second
clause implementation path.

### Per-declaration runtime policy (implemented, then removed)

A four-way `EffectRuntimePolicy` spelled as a tick-suffix attribute on
effect declarations, published through the catalog, with typing errors for
handling `'primitive`/`'intrinsic` effects. Implemented 2026-07-23 and
removed the same day: the syntax had to be restricted to Core, the
compiler still needed a supplier table keyed by pinned symbols, and the
two sources could disagree. A policy only one lockstep-shipped module may
spell is a compiler-internal fact dressed as language surface.

### Compiler-known host list with synthesized fallback clauses

The intermediate design: `HOST_EFFECTS = ['io, 'alloc, 'async]` pinned in
the compiler, MIR synthesizing the fallback clause bodies and the io
tag-dispatch. Worked, but kept per-effect knowledge (pinned symbols, a
supplier table, the request-enum-to-host-op mapping) inside the compiler.
Rejected in favor of self-hosting: the dispatcher is 24 lines of ordinary
Talk, the ambient set is a function signature, and changing host behavior
is a core-source edit.

### Reject `@handle` over raw `'io` until a safe typed request API exists

The original draft. The actual soundness hole was never the raw pointers
but core's trust in reply counts, which clamping closes at ~5 call sites.

## Consequences

- One routing model; the compiler contains no effect names at all. The
  only effect-shaped special case left anywhere is the compile-time
  `'unsafe` capability.
- Which effects are ambient, and what the host does for each, is readable
  (and editable) Talk source in core/Host.tlk.
- Tests and embeddings can intercept, substitute, or observe `'io`,
  `'alloc`, and `'async` requests through ordinary handlers.
- `'io` performs pay a handler search and an indirect call — noise against
  a syscall. Every program carries the small `_with_host` frames and one
  hidden result slot.
- Missing host behavior for a newly ambient effect is a type error in core
  itself (the handler row must match the callback row), not a runtime
  trap.
- `print` remains uninterceptable until it performs `'io` (separate
  decision).

## Implementation notes (2026-07-23)

- Inline IR: `io <op> $a $b $c` replaces the special-cased `io_write`
  (op = checked integer immediate; `CheckedIrKind::Io`).
- `Symbol::WithHost` is the one pinned symbol (`well_known_core_global`,
  minted for `_with_host` at Core module scope). The former pinned
  `'io`/`'async`/`'alloc` effect symbols are gone.
- Typing: `groups.rs` seeds `ambient_effects` from
  `schemes[WithHost].ty`'s callback row (`host_discharged_effects`).
- Entries: `wrap_with_teardown` builds a unit-returning `entry_body`
  chunk (call inner, `GlobalStore` the hidden `result_slot`), wraps it in
  a captureless closure, calls the demanded `_with_host`, reloads the
  result, then runs teardown. Named entries share the path.
- Core: `Host.tlk` (dispatcher + wrapper); `_io_clamp` reply clamps in
  `OS.cwd`/`getenv`/`argc`, `TcpStream.read_string`, and the HTTP read
  loop.
- Black-box coverage in tests/talk_tests.rs: interception with
  perform-counting, delegation to the fallback, nested delegation,
  discontinue, function-value capture with and without a live handler,
  module-init performs under a named entry, inert `'alloc` performs, and
  the lying-handler clamp test.
