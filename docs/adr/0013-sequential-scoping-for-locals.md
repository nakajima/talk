# 0013 — Sequential lexical scoping for locals

Status: implemented (2026-07-04)

## Context

Name resolution ran declare-everything-then-resolve-uses over the whole
tree. That is the right discipline at module scope — forward references
and mutual recursion want letrec semantics — but applied to locals it
hoisted them: every `let` in a block landed in a name-keyed map where
the last same-named declaration won, and uses resolved against the
final map rather than their position in the program.

Locals-hoisting was the single decision behind an accumulated pile of
compensating machinery: per-`let` mini-scopes wrapping only the
right-hand side (level bookkeeping), opened and closed in both passes;
the resolver pass "teleporting" back through stored parent pointers on
exit; the declarer pass duplicating scope creation for blocks, arms,
and nested funcs; and the interim `DuplicateDeclaration` error that
outlawed sequential rebinding (`let x = ...; let x = x + 1`) because
rebinding under hoisting was a miscompile.

## Decision

Locals resolve in a single in-order walk (the resolver pass); module
scope keeps its predeclare-then-resolve discipline.

1. **A binding is visible from just after its initializer to the end of
   its block.** `let x = x` on the right-hand side refers to the outer
   `x`. Implementation: the binder's symbol is minted (and the pattern
   resolved) when the `let` is entered, but it is staged — inserted into
   the enclosing scope only when the decl exits, after its initializer
   resolved.
2. **A later same-named binding shadows from its point of declaration
   on.** Sequential rebinding within one block is legal; insertion may
   overwrite a same-scope name, which is sound because every earlier
   use already resolved. `DuplicateDeclaration` no longer fires for
   rebinding; it remains for genuine duplicates — one pattern binding a
   name twice, or two same-named local funcs in one block — where the
   name-keyed map would silently orphan a binder.
3. **Blocks, function bodies, and match arms are scopes**, created
   fresh by the resolver pass as it enters them. Parameters live in the
   function's scope, visible throughout the body; a body-level `let`
   may shadow a parameter. An arm's binders are visible throughout the
   arm (declared on entry); a `let`'s are not (staged until exit).
4. **Func-valued `let` binders are items** (departure from plain
   sequential `let`, precedented by Rust's `fn`-in-block hoisting and
   JS function declarations): they are hoisted at block entry, so local
   `func a` / `func b` can be mutually recursive regardless of order,
   and `func f` can call itself. This is required because `func` decls
   desugar to func-valued lets before resolution, and local mutual
   recursion is long-standing behavior
   (`local_func_group_is_deeper_than_top_level`). A later plain `let`
   of the same name still shadows the hoisted func sequentially.
5. **Module scope is unchanged**: declaration order does not matter;
   forward references resolve via predeclaration, dependency analysis
   groups bindings as before, and the REPL's top-level redefinition
   behavior (newest declaration wins) is preserved.

Level bookkeeping (the SCC graph's generalization levels and capture
levels) no longer rides on per-`let` mini-scopes: the resolver keeps an
explicit counter — the enclosing-`let` depth — bumped on `let` entry
and restored on exit; resolver-created scopes record it. The observable
levels are unchanged (locked by `resolves_captures` and
`local_func_group_is_deeper_than_top_level`).

## Follow-ups landed on the same branch

- **Resolver test-only machinery deleted.** The resolver's capture
  recording (`ResolvedNames::captures`/`captured`, `Capture`, the
  boundary/binder/level fields on `Scope`) and its SCC dependency graph
  (`scc_graph.rs`, `track_dependency*`, `current_symbol_scope`,
  `unbound_nodes`) had no consumers outside the resolver's own tests —
  the type checker runs its own dependency analysis
  (`types/generate/support.rs`) with its own level constants, and
  closure captures are computed in `flow/captures.rs`. All of it is
  gone; the `Level` type moved to `types/mod.rs`, its real home.
- **Recursive local funcs now compile and run** (they resolved before
  this branch but broke downstream — a pre-existing gap). Three parts,
  each the value-level mirror of the resolver's fn-in-block hoisting:
  the checker pre-binds every func-valued `let` binder in a block to a
  shared monomorphic variable before checking its statements
  (`hoist_local_func_signatures`; `check_local_decl` ties the variable
  to the definition — monomorphic recursion, no generalization inside
  the block); the lowering pre-mints every such binder's λ_G label at
  basic-block entry (`hoist_block_funcs` + `local_func_labels`) so
  bodies reference each other's stable `func_ref`s; and a named local
  func binds directly to its label's value with no `let_…` continuation
  — through a binder var, mutually-referencing funcs would nest under
  each other's lets and cycle the λ_G nesting relation (Property 2).
  Celled (mutated) func binders keep their late-bound cells and are
  excluded; calling one recursively is a diagnosed
  lowering-not-yet-supported, not a crash (`resolve_callee` no longer
  demands a global for an unbound local symbol). `demand` itself now
  returns `Option<Label>`: a symbol with no callable signature is a
  diagnosed `None` its callers abandon well-typedly (`dead_end`),
  instead of the old void-domain placeholder label whose type was a lie
  and panicked the λ_G constructor at the next application.

## What this deleted

- Per-`let` rhs mini-scopes and their paired enter/exit in both passes.
- The declarer pass's local duties: block scopes and arg declarations,
  match-arm scopes and binder declarations, nested-func scope/name/param
  handling, local `let` declaration. The declarer now handles module
  scope and type members only, and tracks block depth solely to tell
  module lets from locals.
- The parent-pointer scope-position reconstruction for mini-scopes.
- The interim `DuplicateDeclaration` error for sequential rebinding.

Symbol id *assignment order* shifted (hoisted func binders mint at
block entry; method/init `self` params mint in resolution order), which
renumbered ids in a handful of resolver tests. No semantics rode on the
numbering.

## Known non-features (unchanged)

- Nominal decls (`struct`/`enum`/…) inside function bodies parse but
  were never cataloged by the type checker; they remain unsupported.
  (Under the old resolver their names resolved and then failed to
  type-check; now the name may also fail to resolve.)
- Or-patterns cannot appear on a `let` lhs — the parser desugars them
  to a single-arm match, so arm-entry declaration covers them.

## Citations (per decision)

- Scope-graph framing — resolution as reachability + visibility over
  scopes with declarations and references; sequential visibility is
  ordered declarations in a scope: Néron, Tolmach, Visser, Wachsmuth,
  ["A Theory of Name Resolution", ESOP 2015](https://web.cecs.pdx.edu/~apt/esop15.pdf).
- Rules 1–2 semantics for `let`: Milner, Tofte, Harper, MacQueen, *The
  Definition of Standard ML (Revised)*, MIT Press 1997 — `let` binds
  for the remainder of its body; shadowing by re-binding.
- Rule 2 ergonomics precedent: the Rust Book / Reference — each `let`
  introduces a new binding shadowing the previous one for the rest of
  the block; idiomatic for staged initialization.
- Rule 4 (func-valued lets as items): the Rust Reference — `fn` items
  declared in a block are visible throughout it; likewise JS function
  declarations. Flagged as the one departure from the plan, forced by
  the pre-resolution desugar of `func` decls to lets.
- Rule 5 (module scope as binding groups): Peyton Jones, *The
  Implementation of Functional Programming Languages*, 1987 —
  dependency analysis into strongly-connected binding groups.
