# How the lowerer works

This directory translates the type-checked AST — by way of the
control-flow-graph MIR built in `src/mir` — into λ_G, the IR
described in `src/lambda_g/README.md`. The detailed source-level
`@_ir`, printed λ_G, and `talk ir` bytecode formats are documented in
`../../docs/ir-and-lambda-g-format.md`. Everything the type checker
learned — per-node types, per-call-site instantiations, member
resolutions — gets spent here; what comes out is a fully monomorphic,
continuation-passing program that the λ_G verifier re-checks and the
VM scheduler can lay out directly. Effect rows are erased in the
process: they did their checking work upstream, and the runtime never
sees them.

Five files: `mod.rs` (the translation itself and the
specialization machinery), `mir_lowering.rs` and `statements.rs`
(walking MIR bodies — blocks, statements, drops), `patterns.rs`
(match compilation), `derive.rs` (synthesized `Showable` witnesses).

## Continuation-passing: the calling convention

λ_G functions never return, so every Talk function lowers to a λ_G
function with one extra parameter: the function to call with its
result (its continuation). Written as pseudocode:

```
// what you wrote
func add(a, b) { a + b }

// what the lowerer produces
func add(a, b, k) { k(a + b) }
```

Sequencing materializes continuations. To lower `f(g(x))`, the lowerer
makes a small function to receive g's result, and runs g first:

```
func after_g(result) { f(result, k) }
g(x, after_g)
```

Statements, argument evaluation, and string concatenation all chain
this way. Two shortcuts keep the output from drowning in tiny
functions: expressions the lowerer can prove pure (variables,
literals, arithmetic on pure operands) are inlined directly with no
continuation, and the optimizer's inlining pass later collapses the
bookkeeping chains that remain.

`return` is a call to the function's return continuation, so an early
return is no different from a normal one. Loops are functions that
call themselves; `break`/`continue` call continuations stashed for the
enclosing loop. Match arms, `if` branches, and everything else that
"joins back up" join by calling a shared continuation function.

## Monomorphization: specialize on demand

The lowerer never translates a generic function in its generic form.
`demand(symbol, theta)` — where theta is a map from the checker's type
parameters to concrete types (the code uses the name `theta`
throughout) — returns the label of the specialized copy, creating a
stub and queueing the body for translation on first request. A
worklist drains until no new (symbol, theta) pairs appear; a cache
makes each pair translate exactly once. The map for a call is built
from the checker's recorded instantiation at that call site, with the
map of the specialization *containing* the call substituted through it
— so generic code calling generic code bottoms out in concrete types
without any runtime dispatch, boxing, or type tags.

Member calls resolve per specialization. If the checker recorded a
resolution at the call node (a direct method, or a conformance
witness), the lowerer demands that target under the receiver's type
map. If it recorded nothing — the member use rode the caller's scheme
as a qualified-type constraint and was discharged per call site — the
lowerer re-resolves the label against the receiver's now-concrete
type: the type's own struct/enum methods first, then protocol
witnesses, mirroring the solver's order. That's how one
`func g(x) { x.go() }` body produces different machine code for each
receiver type that flows through it, each calling the right `go`
statically. The owner's type arguments are recovered from the
receiver's concrete type (owner-theta), so methods of generic structs
specialize correctly too.

## Data representation

- **Anonymous records are tuples.** Fields sort by label; `r.a` is an
  extract at the label's position in the sorted order, computed per
  specialization (a row-polymorphic function learns its concrete row
  from its type map, so the index is always static). Assigning
  through a record path rebuilds the tuple along the path — records
  are values.
- **Structs, strings, and arrays are heap records** with `RecordNew` /
  `GetField` / `SetField` primitives. Construction calls the
  (explicit or synthesized memberwise) init with a blank record whose
  fields are poisoned until the init assigns them — a partially
  initialized struct fails loudly, not silently.
- **Mutating methods** can't mutate in place across a call boundary in
  a value world, so a `mutating` method's continuation carries
  `[result, new_self]` and the *caller* writes the new self back into
  wherever the receiver lived (local cell, record path, …).
- **Mutable bindings are cells** (heap boxes read and written by
  primitive). Top-level bindings that functions mutate are registered
  in `top_level_cells`; a function body that assigns to one simply
  references main's cell as a free variable, and λ_G's normal closure
  rules carry it — no global-variable machinery exists.

## Effects: two calling conventions

Functions whose calls can't escape through an effect use the plain
convention above. A function whose body performs an effect that a
*caller's* handler must receive — determined by a fixpoint over the
checker's tables (which performs route to which lexical handlers,
which functions reference abort-capable functions, minus handlers the
function contains itself) — gets the **abort-capable** shape: after
its regular parameters it takes a normal-return continuation and a
*slot*, an extra continuation representing "the place an abort
unwinds to". Performing an aborting effect calls the slot instead of
the normal return; because both are just continuations, there is no
stack unwinding, no exception tables — an abort is one call.

The convention is infectious in the direction it must be (callers of
abort-capable functions thread the slot through) and contained where
it can be: a function that handles everything it performs stays on the
plain convention, and so do its callers. Resumable handlers
(`continue v`) receive a pair [payload, resume-continuation]; resuming
is calling the second element. Handler capabilities flow to performs
as ordinary closure captures, exactly like the top-level cells.

Constructs the lowering doesn't support yet don't limp along: they
emit a diagnostic and lower to a call of a deliberately bodyless
function (a trap), so running one is loud and type-checking the IR
still succeeds. The λ_G verifier runs after lowering and after every
optimizer pass, so a lowering bug surfaces as a verifier error with a
location, not as a miscompiled program.

## Pattern matching (`patterns.rs`)

Matches compile to decision trees. The compiler works over a matrix of
patterns: pick the leftmost column where the first row actually tests
something; if it's an enum column, emit one `switch` on the variant
tag and split the matrix per variant; literal columns become an
equality chain; tuples and records destructure in place without
branching; or-patterns duplicate rows. Each arm's body is lowered
exactly once into a function taking the arm's bindings — several
switch cases reaching the same arm just call the same function, which
is the CPS rendering of a join point.

## Derived show (`derive.rs`)

When the checker discharged `Showable` structurally (no explicit
conformance), there is no witness function to demand — so the lowerer
synthesizes one in λ_G directly: a chain of string-literal and
sub-`show` calls folded through the `String: Add` witness, printing
`Name(field: value)` for structs and `Name.variant(payloads)` for
enums. Recursive types work because the synthesized witness is itself
demanded through the normal (symbol, theta) cache.

## Further reading

CPS with continuations as ordinary functions and primitives in direct
style is the Thorin arrangement (Leißa, Köster & Hack, CGO 2015); the
translation is a first-order rendering of Danvy & Filinski,
*Representing Control* (1992), leaving administrative redexes to
inlining. Lazy (symbol, theta) specialization is MLton's whole-program
model and rustc's monomorphization collector; running protocols
witness-direct rather than through dictionaries is Jones (PEPM 1994).
The abort-capable convention is capability-passing CPS (Schuster,
Brachthäuser et al., PLDI 2022). Pattern compilation follows Maranget,
*Compiling Pattern Matching to Good Decision Trees* (ML 2008), with
join points per Maurer, Downen, Ariola & Peyton Jones (PLDI 2017).
Derived instances as compiler-supplied class defaults go back to
Wadler & Blott (POPL 1989).
