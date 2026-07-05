# 0015 — Typing publishes, lowering reads

Status: implemented (2026-07-04)

## Context

One week of iterator work surfaced ~11 compiler bugs. Each was an
instance of one disease: **the same fact implemented in more than one
place** — requirement signatures copied into the lowerer
(`requirement_sigs`), the lowerer re-binding conformance rows the solver
had already bound (`resolve_witness`), a ~75-line re-implementation of
member lookup in `resolve_callee`'s unresolved arm, a `mutating` registry
re-encoding what `&mut self` in signatures already said, and four
parallel signature carriers (schemes / `Requirement.sig` /
`InherentMember.sig` / raw catalog types) each hand-maintaining its own
quantify–freshen–sanitize lifecycle and each missing steps the schemes
path already had.

Production compilers split on the cure. Swift resolves a conformance
once in Sema and SIL *carries* the `ProtocolConformanceRef`; rustc's
codegen re-resolves, but through the same query-backed
`Instance::resolve` the type system used. talk's HIR had already taken
the Swift bet for types (`ty` baked on every node). This ADR finishes
that journey for dispatch, signatures, and calling conventions.

## Decision — four invariants

**I1. The node carries the resolution.** The solver publishes, per call
node, the resolved target (`member_resolution`) AND the complete θ
(`instantiation`): method generics, owner-param bindings for direct
methods, instance-head bindings for inherent members, conformance-row
bindings for committed witnesses, Self/assoc bindings for defaults.
Entries may hold vars/projections at solve time; finalize zonks and
normalizes them. Lowering reads θ off the node and demands.

**I2. One signature carrier.** Every polymorphic callable type is a
`Scheme` in the schemes table — top-level funcs, methods, extend
witnesses, protocol requirements, inherent extend members, enum
constructors. `Requirement` is `{symbol, has_default}`; `InherentMember`
is `{symbol, params, self_args}` (the instance-head pattern only). The
catalog carries structure, never signature copies. One quantification
(collection or `check_extend`, which also quantifies leftover effect
rows via `quantify_leftover_eff_vars`), one instantiation discipline,
one sanitize/export/import path.

**I3. Nothing var-shaped crosses a module boundary.** Catalog
finalization bakes and sanitizes every embedded type through
`TypeCatalog::for_each_embedded_mut` — the single authority for "types
the catalog carries" (fields, variant ctor schemes, effect sigs,
conformance self_args/assoc, all predicate positions, aliases). A
debug-mode assertion at `Driver::module()` re-runs the same walk, so a
future catalog field that skips it fails at every module export. This is
GHC's `.hi`-tidying discipline (interface files ship tidied, zonked
types).

**I4. Conventions derive from signatures.** The inout calling convention
(`mut` methods return `[result, Self]`) is computed once, totally, from
the schemes table (`derive_mutating`: first param an exclusive borrow,
minus `'heap` receivers). There is no per-declaration-kind registration
to forget — the class of "the registry missed a symbol kind" is gone,
and imported symbols are covered uniformly.

## The finding: one honest carve-out (the rustc case)

Full Swift-model purity is impossible under dictionary-free
monomorphization, and the probe run proved exactly where: a member use
that rode its binder's scheme (`func call_go(x) { x.go() }` — a
HasMember context predicate) has ONE node serving MANY specializations
with different targets. No single annotation can carry that. Witness
selection there is inherently a monomorphization-time decision — rustc's
`Instance::resolve` makes the same move. Two selector sites remain in
lowering, both documented as such:

- `resolve_callee`'s unresolved-member arm (scheme-context predicates);
- `resolve_witness`'s deferred branch (generic receivers and
  protocol-static operators, where the solver recorded the requirement
  symbol as a placeholder).

The line: **the solver's published θ is authoritative wherever it
committed; the monomorphizer selects only where polymorphism deferred
it.** `resolve_witness` reads the node θ (filtered to the target's own
parameter space, keeping specialization keys stable) when the resolution
names a committed witness, and derives from the θ-substituted head only
for deferred/existential cases.

## Deleted

- `requirement_sigs` (the lowerer's copy of every requirement sig).
- `resolve_witness`'s row re-binding and assoc re-substitution for
  committed witnesses.
- `owner_theta` at direct member calls AND constructions (both publish
  on the node; the helper survives only inside the monomorphization
  selector, where no node θ can exist).
- Both hand-registration sites of the `mutating` registry (now derived).
- `Requirement.{sig, predicates, eff_params, generics}`,
  `InherentMember.sig`, and their import/export/finalize plumbing.

## Fixed as a by-product

Inherent extend members with method generics and/or closure params were
latently broken exactly like `map` had been (nothing freshened them —
`vm_matches_evaluator_on_generic_inherent_extend_member_with_closures`
failed before, passes now), and extension-method schemes now quantify
their closure rows instead of sharing one module-wide row var.

## Decided / deferred (the ledger — nothing is "known" without a home)

- **Effect-generic closure storage — DONE (day 3)**: effect parameters
  on struct types (docs/effect-params-on-structs-plan.md). Closure
  fields' free row tails quantify as implicit effect params at
  collection; constructions instantiate them (fresh open rows carried as
  `Ty::Eff` args on the nominal head — Koka-style kinded type
  arguments); member reads splice the INSTANCE's row back over the
  field's tails (`Ty::substitute_eff_rows`); annotations append fresh
  rows (a bare head means "some rows", pinned by whatever it meets);
  HIR bake erases eff args (capabilities ride closure envs at runtime).
  Sound in both directions — no cross-construction contamination, no
  laundering through a struct or a module boundary — five tests pin it,
  including a both-engines handled/resumed stored-closure run. v1 scope
  residuals (enums, Self-in-methods, explicit inits) are listed in the
  plan doc.
- **Existential dispatch** stays erased/substitute-only (witness tables
  over `Any` receivers) — the same carve-out Swift makes for opened
  existentials.
- **`&&T` DECIDED (addendum, same day)**: nested borrows collapse — a
  borrow is a permission view, and a view of a view is one view at the
  weaker permission (`&(&mut T)` ≡ `&T`). Canonicalized in
  `TyFold::fold_children` (every substitute/zonk/sanitize inherits it)
  and `normalize_ty` (vars resolving to borrows); concrete perms only,
  var perms wait for defaulting. Diagnostics render the canonical form.
- **Container element deep-drop — DONE (addendum, same day)**: Array
  conforms to Deinit in core; the deinit take-loop re-owns each element
  behind an `_is_unique` gate (CoW: exactly the last reference tears
  down), recursing structurally. En route: Deinit dispatch θ binds the
  conformance row (generic witnesses were erased); the self-recursion
  guard is θ-aware (nested arrays dispatch); the drop-glue owns field
  teardown AFTER the hook (Rust Drop::drop model — bodies never
  schedule consumed-self drops); the existential drop-witness index
  resolves through the entry unit's catalog; the for-loop desugar names
  RVALUE iterables so their buffers drop. ~12 formerly-fenced tests now
  assert strict balance.
- **Generic ownership — DONE (day 3)**: generic (`Param`/`Proj`-typed)
  values are owned. The LAST consume moves; every earlier consume is an
  implicit copy (tier-2 auto-clone: CheapClone retains, Copy is free,
  decided per instantiation at lowering). Liveness decides which is
  which (`flow::liveness::dead_after` — conservative in sibling
  branches, so over-approximation only costs a balanced retain+release,
  never a move before a live use; moving early and reusing would read
  memory the consumer may already have freed). Zero consumes → generic
  bindings and by-value params get scope-exit candidates, classified
  once over the generic body and elided per θ. Impure `@_ir` binds
  (auto-cloned generics) lower continuation-style through `lower_args`.
  The `eval_expecting_generic_ownership_leak` fence is DELETED — every
  test asserts strict allocation balance.
- **Temporary teardown — DONE (day 3, fell out of the above)**: a
  call/construct temp that is only BORROWED by its consumer (e.g.
  `print(&T)` of an rvalue concat) was never freed. The MIR builder now
  emits a `TemporaryEnd` drop candidate per temp at its full
  expression's end (before delivery/exit statements, so the exit
  machinery's candidate adjacency holds); flow classifies Dead
  (consumed — a checker-level static set, per body) or Static; lowering
  releases Static ones. En route, four more root causes fell:
  the protocol-static call form (`Add.add(a, rhs)` — the operator
  desugar) mis-aligned args against the scheme with self stripped,
  consuming borrowed receivers; heap-constructor rvalue args move into
  the region (ledger rule B) and their temps count as consumed;
  zero-length statics interned at the region's end aliased the first
  heap allocation (they now reserve a byte); derived `show`'s
  accumulator chain borrowed-and-leaked every intermediate (each
  continuation now frees the superseded acc). New `@_ir { free $0 }`
  instruction + core `_free(ptr)`; `open_path` frees its NUL copy; raw
  io examples/tests free their buffers.
- **Block-scoped alias double-free — FIXED (day 2)**: tail-position
  blocks are real MIR (`tail_expr` no longer swallows them), so moves
  inside them are visible; `join_depth` keeps nested tail deliveries as
  continuations rather than returns.
- **completion.rs display substitution**: read-only rendering of
  schemes; acceptable.

## Precedents

- Swift: Sema-resolved `ProtocolConformanceRef` carried in SIL;
  Sema-set types on AST acknowledged as the pattern to contain.
- rustc: `Instance::resolve` at codegen through the shared trait solver;
  `TypeckResults` as the one canonical side table.
- GHC: `.hi` interface tidying (no typechecker-internal state escapes a
  module); Core Lint as the between-stages type check (λ_G's T-App
  construction check is the same discipline, eager).
