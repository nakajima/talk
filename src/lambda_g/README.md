# How the λ_G intermediate representation works

This directory is the compiler's middle language. The lowerer
(`src/lower`) translates type-checked Talk into it; the bytecode VM
(`src/vm`) runs what comes out. For the exact textual syntax printed by
`talk lower`, and how it differs from `@_ir` source splices and
`talk ir` bytecode listings, see `../../docs/ir-and-lambda-g-format.md`.
The whole design is one bet: **if the only thing in the language is
small functions calling each other, then every compiler problem becomes
a question about functions** — and those questions have simple answers.

## Everything is a function call

There are no statements, no blocks, no `if`/`loop`/`return` constructs
in the IR. A program is a flat collection (we say "soup") of named
functions, each with parameters, and a body that is a single
expression — almost always a call to another function.

Control flow falls out of that:

- An `if` becomes: call `then_branch()` or `else_branch()` depending
  on a boolean (a `branch` primitive picks the callee).
- A loop becomes a function that calls itself.
- "Do A, then B" becomes: A is told to call B when it finishes.

That last point is the one habit to internalize: **functions here
never return**. Instead, every function takes an extra argument — a
function to call with the result. Returning *is* calling that
argument. (The standard name for this style is continuation-passing,
but "tell me where to go next" is all it means.) Once returns are
explicit calls, early return, effect handlers that abort, and
suspending on io all stop being special — they're just calls to a
different "where to go next" than usual.

## The pieces

- `program.rs` — the soup itself: a map from labels to functions. A
  function's *name* and the *variable that refers to it* are the same
  identifier, so there's no bookkeeping to keep them in sync. Bodies
  may be temporarily unset while building recursive functions
  (create both, then fill in bodies that mention each other).
- `expr.rs` — expressions: variables, constants, calls, tuples and
  field extraction, plus direct-style primitives (arithmetic, memory,
  io) that compute a value without being calls. Expressions are
  immutable, and identical expressions are stored exactly once and
  compared by id (so "is this the same expression" is a pointer
  comparison, and rewrites that produce an existing expression reuse
  it for free).
- `fv.rs` — for each function, which outside variables does it
  mention, directly or through the functions it references? Computed
  lazily and cached, recomputed only for functions an edit actually
  touched. Nearly everything else is built on this one query.
- `nest.rs` — the nesting tree. Although functions live in a flat
  soup, you can recover a sensible "who belongs inside whom" structure
  by looking at variable use: if `inner` mentions `outer`'s parameter,
  `inner` must sit inside `outer`. The tree built from that fact is
  what the VM scheduler walks to lay out code, and it plays the role
  the classical control-flow-graph dominance analysis plays in other
  compilers — except it never goes stale, because it's derived from
  the code itself.
- `subst.rs` — copy a function while replacing some of its variables.
  Inlining, specializing a generic, and unrolling a loop are all this
  one operation. The free-variable cache makes it cheap: anything that
  doesn't mention a replaced variable is shared, not copied.
- `check.rs` — the verifier. After lowering and after every pass it
  re-checks two things: every call's arguments match the callee's
  parameter types, and the "who's inside whom" relation has no cycles.
  Bugs in the lowerer get caught here, loudly, instead of as
  miscompiled programs.
- `eval.rs` — the reference evaluator: a slow, direct, obviously-
  correct interpreter for the IR. It exists to keep the fast engine
  honest — the test suite runs programs on both this evaluator and
  the bytecode VM and requires identical results.
- `print.rs` — renders the soup as text in plain function syntax,
  with helper continuations nested under the function that owns them
  (`talk lower file.tlk` and the IR snapshot tests use it).
- `sets.rs` — small immutable sets of labels, stored once and compared
  by id, because free-variable sets are tiny and get compared
  constantly.

## Why this shape

Three things get dramatically simpler in exchange for the unusual
no-returns style:

1. **One optimizer.** Inline, specialize, peel a loop — each is "copy
   this function with these substitutions". There is no separate
   machinery per transformation, and no analysis to patch up
   afterward; the next free-variable query just sees the new code.
2. **Effects without a runtime.** Handlers, aborting out of a deep
   call, and resuming a suspended computation all reduce to passing a
   different "where to go next" function. The VM needs no stack
   unwinding, no exception tables.
3. **Honest verification.** Because the IR is typed and tiny, a full
   re-check after every pass is affordable, and the two-engine test
   policy (evaluator and VM must agree) pins the semantics down from
   both sides.

## Further reading

The IR is a faithful implementation of Leißa & Griebler, *SSA without
Dominance for Higher-Order Programs* — the full text lives in
`ssa-paper.md` at the repository root and the source comments cite its
sections and equation numbers throughout. Its ancestors are the Thorin
IR (Leißa, Köster & Hack, CGO 2015) and MimIR (POPL 2025); the
evaluator follows Reynolds' 1972 definitional-interpreter recipe; the
per-pass verifier is in the spirit of LLVM's module verifier (Lattner
& Adve, CGO 2004).
