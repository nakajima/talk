# Sequential lexical scoping for locals

Status: implemented 2026-07-04 (branch `worktree-sequential-scoping`);
recorded as [ADR 0013](adr/0013-sequential-scoping-for-locals.md). One
departure surfaced during implementation: func-valued `let` binders are
hoisted block-wide (Rust's `fn`-in-block item behavior) because `func`
decls desugar to lets before resolution and local mutual recursion is
long-standing, test-locked behavior. Details in the ADR.

## Context

Name resolution today runs declare-everything-then-resolve-uses over the
whole tree. That is the right discipline at module scope — forward
references and mutual recursion want letrec semantics, resolved into
binding groups by the SCC graph — but it is applied to locals too, which
hoists them: every `let` in a function lands in a name-keyed map where
the last same-named declaration wins, and uses resolve against the final
map rather than their position in the program.

Locals-hoisting is the single decision behind an accumulated pile of
compensating machinery and user-facing jank:

- Per-`let` mini-scopes that wrap only the right-hand side (level
  bookkeeping), opened and closed in *both* passes.
- The resolver pass reconstructing its scope position by "teleporting"
  through stored parent pointers when it exits those mini-scopes.
- Methods sharing one parameter scope (every method's `self` lives in
  the same map).
- The let-shadowing miscompile fixed on unicode-strings (blocks were
  not scopes; every use of `y` in a function silently bound to the last
  `y` declared) — and the interim `DuplicateDeclaration` error that fix
  introduced, which outlaws sequential rebinding
  (`let x = ...; let x = x + 1`) even though it is legal, useful, and
  sound in ML and Rust.

The DeclaredLocal flavor of this and the module scheme-export collision
fixed alongside unicode were the same family of defect: per-symbol facts
collapsing into name- or id-keyed maps that forget entries.

## Target semantics (user-facing rules)

1. **A binding is visible from just after its initializer to the end of
   its block.** `let x = x` on the right-hand side refers to the outer
   `x`.
2. **A later same-named binding shadows from its point of declaration
   on.** Sequential rebinding within one block is legal; uses before the
   shadow keep the earlier binding. The interim `DuplicateDeclaration`
   error is removed.
3. **Blocks, function bodies, and match arms are scopes.** Parameters
   live in the function's scope, visible throughout the body, and a
   body-level `let` may shadow a parameter. Each method body is its own
   scope.
4. **Module scope is unchanged**: declaration order does not matter;
   forward references resolve via predeclaration, and dependency
   analysis groups bindings for the checker as today. The REPL's
   top-level redefinition behavior is module-scope behavior and must not
   regress.

## Citations (per decision)

- Scope-graph framing — resolution as reachability + visibility over
  scopes with declarations and references; sequential visibility is
  ordered declarations in a scope: Néron, Tolmach, Visser, Wachsmuth,
  ["A Theory of Name Resolution", ESOP 2015](https://web.cecs.pdx.edu/~apt/esop15.pdf)
  (verified 2026-07-03; the paper's calculus comes with a sound and
  complete resolution algorithm).
- Rule 1 and 2 semantics for `let`: Milner, Tofte, Harper, MacQueen,
  *The Definition of Standard ML (Revised)*, MIT Press 1997 — `let`
  binds for the remainder of its body; shadowing by re-binding.
- Rule 2 ergonomics precedent: the Rust Book / Reference — each `let`
  introduces a new binding shadowing the previous one for the rest of
  the block; idiomatic for staged initialization.
- Rule 4 (module scope as binding groups): Peyton Jones, *The
  Implementation of Functional Programming Languages*, 1987 — dependency
  analysis into strongly-connected binding groups; talk's SCC graph is
  already this.
- No novel departures: the target is deliberately the boring, standard
  model. The only talk-specific extension is that the same walk also
  records captures and dependency edges (which `lookup` already does
  today).

## Implementation shape

One in-order walk over function bodies with an environment stack:

- Push a frame per block / function body / match arm; pop on exit.
- A `let` inserts into the top frame *at its declaration point, after
  its right-hand side is resolved* (rule 1). Insertion may overwrite a
  same-frame name — sound now, because all earlier uses already
  resolved (rule 2).
- Lookup walks frames innermost-out; capture and dependency-edge
  recording happen in the same walk, as `lookup` does today.
- Module scope keeps the existing predeclare pass (nominals, effects,
  aliases, public values) and SCC grouping. `DeclDeclarer` shrinks to
  that plus type-member collection.

**This deletes more than it adds:**

- Per-`let` rhs mini-scopes and their paired enter/exit in both passes
  (`decl_declarer.rs`, `name_resolver.rs`).
- The parent-pointer scope-position reconstruction ("teleporting").
- `DeclDeclarer`'s local-declaration duties (declare_pattern for
  locals, block/arm scope creation for resolution purposes).
- The shared method-parameter scope.
- The `DuplicateDeclaration` error and its tests' interim expectations.

The LSP/workspace still gets a scope tree (`phase.scopes`); it is
emitted from the same walk and gains honest extents (a binding's range
starts at its declaration, not at block top).

## Care points

These piggyback on the current structure and need characterization
tests *before* restructuring:

- **`Scope.level` consumers** — capture levels
  (`capture_binder_level`, `nearest_capture_binder_from`) and whatever
  the checker reads for let-generalization; today `bump_level` fires
  per `let`. Decide whether levels come from a counter in the walk or
  from closure boundaries only, and lock behavior with tests first.
- **Closure captures of shadowed names** — a closure capturing `x`
  where `x` is later shadowed must capture the binding visible at the
  closure, not the shadow.
- **Match-arm binders** (including or-patterns, which declare only in
  their first alternative today).
- **Synthesized nodes between passes** (generated inits) — the walk
  must tolerate nodes with no pre-made scope; under a single walk this
  becomes a non-issue but the tests should exist first.
- **REPL redefinition** at module scope.

## Sequencing (each checkpoint `cargo test` green)

1. **Characterization matrix** — tests for: `let x = x`, sequential
   rebinding (expected to *fail* until step 4 legalizes it), sibling
   and nested shadowing, param shadowing, capture-of-shadowed-name,
   arm binders and or-patterns, REPL/module redefinition. Lock current
   intended behavior; mark the sequential case as the change to come.
2. **Environment-stack resolution for function bodies only** — single
   walk; module scope untouched. Both old and new agree on everything
   in the matrix except sequential rebinding.
3. **Delete the scaffolding** — mini-scopes, teleport, declarer local
   duties, shared param scope. Net-negative diff expected.
4. **Legalize sequential rebinding** — remove `DuplicateDeclaration`,
   flip the matrix case, add both-engine value tests
   (`let x = 1; let x = x + 1`).
5. **Sweep** — LSP scope extents, diagnostics wording, docs/adr entry
   recording the model and citations.
