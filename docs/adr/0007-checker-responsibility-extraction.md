# ADR 0007: Separating the checker's responsibilities

## Status

Stages 0-2, the `CatalogBuilder` extraction part of Stage 3, and Stage 4 are implemented. Stage 3's stronger read-only-catalog goal remains incomplete. Supersedes the framing of ADR 0006: that ADR's file split is **navigability** (and a way to make the seams below visible), not the architectural fix. This ADR targets the actual coupling.

## Context

Before ADR 0006/0007, `Checker` (`generate.rs`) was a ~30-field god-object whose methods all took `&mut self`. ADR 0006 spread that work across files for navigability; this ADR records the responsibility split that followed. A read of the original code (footprints measured, not guessed) found three responsibilities, one shared subsystem, and borrow-checker-induced entanglement — which is why the old shape was not merely sloppy code.

### Three responsibilities, one shared `VarStore`

1. **Type elaboration** — annotation AST → `Ty`. `lower_annotation`,
   `lower_nominal_path`/`_child`, `lower_type_alias`, `lower_associated_projection`,
   `lower_any_annotation`, object-safety checks. Footprint: `store` (mints fresh
   row/effect tails), `catalog` (read, to resolve nominals/aliases),
   `self_types` (the `Self` in scope), `alias_stack`, `type_aliases`, `level`,
   `errors`. **Cross-cutting**: called from collection (15 sites) *and* from
   expression/statement/pattern checking (10 sites). Almost constraint-free —
   exactly one emission (nominal well-formedness).

2. **Catalog collection** — declaration AST → `TypeCatalog`. `register_struct`/
   `_enum`/`_protocol`/`_effect`/`_extend`, requirement & alias collection.
   **Solver-free** (zero constraint emissions). Uses elaboration to lower
   signatures. Mutates the catalog and produces the work-lists consumed by checking (`decls`, `stmts`, `destructuring_lets`, `extends`, `protocol_defaults`).

3. **Constraint generation + solving** — `check_*`/`infer_*`, `run_solver`,
   `finalize`. Uses elaboration and reads the catalog. Owns the inference
   context (the `ret`/`eff`/`self`/`binder`/`handler` stacks) and the ~14
   output maps.

`TypecheckSession::run` now executes these in clean temporal order: collect (Phase 1) -> check groups/extends/defaults/statements (Phase 2) -> coverage + finalize (Phase 3). The collect -> check handoff is a `Collected` value, not a convention plus a boolean flag; nominal well-formedness obligations are accumulated by the `Elaborator` and either dropped during collection or emitted during checking.

### Remaining weak boundary

The collection -> checking transition is typed, but catalog immutability during checking is not fully enforced. `CatalogBuilder` owns collection, yet `BindingGroupChecker` still borrows the catalog mutably for the few checks that write back inferred associated-type bindings or register checking-time bounds. So the old phase-validity hazard is reduced, not eliminated.

### Why it is partly borrow-checker-induced (not just sloppiness)

Elaboration **reads** the catalog while collection **writes** it, and both
**mint into the same `VarStore`**. Holding those as one `&mut self` sidesteps
the aliasing entirely. Split into separate structs that borrow `&mut VarStore`
and the catalog, and the borrow checker bites: a `CatalogBuilder` holding
`&mut catalog` cannot also lend `&catalog` to an elaborator mid-build. The
single context is the path of least resistance — the same reason real checkers
converge on one monad (GHC's `TcM`, rustc's `FnCtxt`). So the target is **not**
"abolish the shared context"; it is "stop conflating elaboration and catalog
construction with it, and make the phase boundary a type."

## Research basis

- Jones, *Typing Haskell in Haskell* (2000), §11.2–11.6: inference is staged —
  assumptions/environment first, then dependency-ordered binding groups. The
  collect-then-check split is this staging; making it a value handed between
  phases (not a mutated field) is faithful to it.
- Dunfield and Krishnaswami, *Bidirectional Typing* (2021): checking is a
  judgement over an explicit context Γ. The `self`/`ret`/`eff` stacks are an
  implicit Γ; an explicit `Ctx` is the bidirectional shape.
- Pierce & Turner, *Local Type Inference* (2000): elaboration of type
  annotations is its own operation, separable from constraint solving — matching
  the finding that elaboration here is almost constraint-free.

(The single-checker-monad pattern, GHC `TcM`, is the deliberate counterexample:
a shared mutable context is legitimate. This ADR narrows, not abolishes, it.)

## Decision

Target architecture — three units over a **shared, sequentially-owned**
`VarStore`:

- `Elaborator` — borrows `&mut VarStore`, `&TypeCatalog`, an `&mut errors`
  sink, and a small `Self`/alias scope; turns annotations into `Ty`. Used by
  both the builder and the checker.
- `CatalogBuilder` — owns catalog construction, uses an `Elaborator`, mutates the session-owned catalog during collection, and returns a `Collected { decls, stmts, destructuring_lets, extends, protocol_defaults }` work list.
- `BindingGroupChecker` / `BodyChecker` — constructed from the collected work and shared session state; drive the solver and hold inference state. They mostly read the catalog, but still mutate it for inferred associated-type bindings and checking-time bound registration.

Staged so each step is independently shippable and the risky ones come last:

1. **Stage 0 — file split (ADR 0006).** *Implemented.* `generate.rs` became a
   `generate/` directory of phase-named files. Navigability; surfaces each
   method's field footprint so later stages are mechanical. Low risk.
2. **Stage 1 — make the phase boundary a value.** *Implemented.* `run` now builds a `Collected<'a>` work list during collection and passes it into checking. `Collected` carries everything Phase 1 produces that Phase 2/3 consumes — `decls`, `stmts`, `destructuring_lets`, `extends`, `protocol_defaults` — so that part of the boundary is a type, not a comment plus sequential mutation. The pure work-list fields (`extends`, `protocol_defaults`) left the session state entirely.

   Two goals the original sketch put here turned out to belong later, and the implementation confirmed why:
   - **Nominal well-formedness emission belonged in Stage 2.** Threading a phase flag through recursive annotation lowering would have been churn. Stage 2 instead made elaboration return obligations, so collection can drop them and checking can emit them.
   - **Catalog immutability during checking belonged in Stage 3.** With one mutable checker context it could only be a convention; extraction was needed before the type system could enforce anything stronger.
3. **Stage 2 — extract `Elaborator`.** *Implemented* (`elaborate.rs`). The
   `lower_*` methods (plus object-safety checks and alias lowering) moved onto
   an `Elaborator` that borrows *disjoint* session/checker fields — `&mut store`,
   `&catalog`, `&mut errors`, `&type_aliases`, `&mut alias_stack`,
   `&self_types`, `&resolved`. The caller builds one inline per top-level
   lower, drives it, drains it, drops it. **The anticipated borrow-checker
   fight did not materialise**: disjoint field borrows + a leaf-scoped
   elaborator compiled first try, with no change to who owns the store.

   The architecturally meaningful win landed: **the elaborator is
   constraint-free.** Nominal well-formedness is no longer emitted mid-lower;
   it is *accumulated* as obligations the checker drains and discharges. Two
   shared helpers (`nominal_params`, `nominal_predicates_for`) became
   catalog-only free fns so the elaborator and the collector/checker share them.

   Honest limits of what shipped:
   - **The `enforce_well_formedness` flag is gone.** The obligation buffer became the phase signal: collection drops obligations, checking drains them into wanteds.
   - **The elaborator borrows rather than owns its footprint.** That made the extraction low-risk and explicit, but the session still owns the underlying store, catalog, diagnostics, alias stack, and self-type context.
   - **Cross-module reuse remains limited.** The lowerer does not need annotation elaboration; the real shared rule was associated-projection reduction, now factored as `solve::reduce_projection`.
4. **Stage 3 — extract `CatalogBuilder`.** *Partially implemented.* Collection moved onto `CatalogBuilder`, which borrows the session's `VarStore`, `TypeCatalog`, diagnostics, alias state, and self-type context, and returns `Collected`. This made catalog construction a separate module with a declared footprint. The stronger goal — constructing the body checker from an immutable catalog — remains incomplete because checking still writes inferred associated-type bindings back into conformance rows and registers some checking-time bounds.
5. **Stage 4 — `Ctx` for the inference stacks.** *Implemented.* The four
   pure-inference stacks (`ret`, `eff`, `handler_ret`, `binder`) became a
   single immutable `Ctx` threaded by `&` (last parameter) and *extended* on
   scope entry, so the call stack is the scope stack — DK 2021's Γ. The four
   `Vec` fields left the checker state, all push/pop pairs are gone, and the
   `handler_ret` save/clear/restore dance around closures collapsed to a
   `Ctx::enter_function` that simply omits it (an immutable context passed
   down cannot affect the caller's). The old mutable binder/effect stack helpers are gone; `Ctx::with_binder` now returns an extended immutable context.
   No borrow-checker fight: `&mut self` (engine) + `&Ctx` (scope) don't alias.

   The other two stacks (`self_types`, `alias_stack`) stayed in session/checker state on purpose — they are *elaboration* context (the `Self` in scope, the alias recursion guard), already borrowed by the `Elaborator` (Stage 2), not inference state. They move only when elaboration/catalog ownership moves further.

## Risks and honest assessment

- **The remaining Stage 3 risk is semantic, not borrow-checker mechanical.** `CatalogBuilder` compiled with disjoint borrows, but checking still mutates the catalog in a few places. Making the checker catalog truly read-only requires deciding where inferred associated-type bindings and checking-time bounds should live.
- **It is multi-stage and behavior-must-not-change.** The safety net is `types_tests.rs` + the suite; there are no unit tests on checker internals, so each stage leans on integration coverage.
- **Diminishing returns are real.** The typed `Collected` boundary, extracted `Elaborator`, extracted `CatalogBuilder`, and immutable `Ctx` removed most accidental coupling. The remaining mutable catalog writes should be changed only if their locality cost outweighs the churn.

## Recommendation

**Do not pursue more separation unless the remaining catalog writes cause concrete friction.** The high-value work is done: the file split surfaced the seams, `Collected` made the collect -> check handoff explicit, `Elaborator` removed constraint emission from annotation lowering, `CatalogBuilder` owns collection, and `Ctx` removed mutable scope stacks. The remaining defect is narrower: checking still mutates catalog entries for inferred associated-type bindings and some bounds.

## Consequences

- A typed collect -> check boundary for the work-lists: collection returns a value the checker consumes, instead of Phase 1 mutating work-list fields Phase 2 reads.
- Elaboration is a unit with a declared footprint and no direct constraint emission; nominal well-formedness is an obligation returned to the caller.
- Catalog collection has its own module, but the catalog is not yet read-only during checking.
- Inference scope is an immutable `Ctx`, so scope entry is ordinary value extension rather than push/pop state.
