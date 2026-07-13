# How the flow checker works

This directory is the flow-sensitive companion to the type system's
substructural core. Permissions and grades live in types (`src/types`);
this pass answers only the flow-sensitive questions — where each value
moves, where borrows end, where drops go — as a forward dataflow analysis
over each body's MIR CFG (ADR 0010). Its inputs are the typed tree
(`src/typed_ast`) and the structural MIR store built by
`lower::mir::build_checked`; its outputs are per-point drop elaborations
and runtime move sets written onto that store (which lowering then
consumes as *checked* MIR), editor-facing `FlowFacts`, and ownership
diagnostics. `check_flow` in `mod.rs` is the entry point.

## The cross-layer contracts

Three invariants connect this module to its neighbors. Each is easy to
break from the other side of the seam, so they live here rather than in
scattered comments.

1. **Lowering does not re-analyze ownership; it reads flow's
   annotations.** The flow pass classifies every scheduled drop at its
   program point (`drops.rs`: `Static`, `Dead`, `Conditional`, `Open` —
   rustc's drop-elaboration categories) and stores the classification on
   the MIR statement. Lowering reads it straight off the statement
   (`lower/mir_lowering.rs::drop_elaboration_at`) and emits exactly what
   it says. If lowering ever needs an ownership fact that isn't
   annotated, the fix is to record it here, not to re-derive it there.
   (The old residual — `lower_early_exit_then`'s fallback drop stack —
   was deleted per plan track 7.1: early exits now lower exclusively
   from the block's trailing `EarlyExit` candidates, and an unelaborated
   needs-release candidate is a lowering diagnostic, not a type-directed
   guess. Lowering's `Ctx::drop_stack` survives only as value-level
   metadata — a symbol's concrete type, drop-flag keys, and deinit-self
   bit — consulted when resolving a flow-authorized candidate.)

2. **`GradeView` is the single owned / object / borrowed authority.**
   `grades.rs` defines what needs a drop, what is trivially copyable,
   what is a `'heap` object handle, and what contains a borrow. Lowering
   builds its own `GradeView` per unit and asks the same questions
   (`lower/statements.rs::grade_views`) — it must agree with the flow
   checker's answers, or scheduled drops stop matching emitted ones.
   Likewise `place.rs::place_for_expr` is the one definition of "what
   place does this expression touch"; flow and the MIR builder share it
   so drop schedules join up.

3. **Embedded node copies mirror the typed tree's facts.** MIR
   statements embed clones of typed expression nodes. Flow records
   consume and auto-clone flags per node id during its recording pass;
   `mir_annotate.rs` then bakes those flags onto every embedded copy
   inside the checked MIR body, so diagnostics and expression lowering
   read the same typed facts whichever copy they look at. Candidate
   elaborations and runtime move sets are not mirrored — they were
   written directly at their MIR program points and stay there.

### The one sanctioned dual: pre-monomorphization needs-drop

Flow runs once over a generic body, before any specialization exists, so
generic-typed values are deliberately split between the two layers:

- `GradeView::needs_drop` answers **false** for `Ty::Param`/`Ty::Proj`
  (`grades.rs`, `contains_owned`): moves of generic-typed values go
  untracked at flow.
- The MIR builder still classifies generic-typed places like owned ones
  and mints **speculative** drop candidates for them
  (`lower/mir.rs::owned_param_locals`, `temp_rvalue_aggregate`).
- Lowering re-filters per specialization: `lower_drop_value_then`
  (`lower/statements.rs`) checks `needs_drop_type` on the concrete,
  θ-substituted type and elides the drop when that instantiation doesn't
  need one.

This is the only place the two layers are *supposed* to disagree about a
type. Don't "unify" it: making flow answer per-instantiation would mean
re-running the checker per specialization, and making the builder skip
generic candidates would leave droppable instantiations with nothing to
elide.

## The engine: three passes per body

`cfg.rs` checks every stored body (and a combined top-level `main` body)
with the same three-phase scheme (`check_body`); which phase is running
is the explicit `Pass` enum threaded through the transfer functions:

1. **`Pass::Fixpoint`** — a silent worklist run: `MoveState` joins at
   block entry from all predecessor exits until entry states converge.
   `break`/`continue`/`return` are edges, so their states reach the loop
   exit / loop head / function exit. May-facts (`moved`,
   `initialized_any`) union at joins; must-facts (`moved_all`,
   `initialized_all`) intersect.
2. **`Pass::Record`** — one more transfer over the converged states:
   editor facts, statement/terminator runtime move sets,
   consume/auto-clone flags, and per-point candidate drop elaborations
   are written; then `mir_annotate` mirrors the expression flags onto
   embedded copies (contract 3).
3. **`Pass::Report`** — the same transfer reporting errors, with the
   checked facts already in place. Each block is visited once, so
   nothing double-reports.

Outside the engine the checker rests at `Pass::Report`: `check_flow`'s
whole-module pre- and post-passes are error-only walks.

Body roles split the work: stored function bodies do all three passes;
each file's transient top-level body reports errors only; the combined
`main` body (what lowering actually executes) records only, so facts
aren't duplicated. Statement-embedded handler bodies and trailing-closure
blocks are *not* special-cased: the MIR builder gives them scaffold CFG
blocks under `Terminator::Handler`, and the engine flows through the
body/join edges as the may-execute approximation.

## File map

- `mod.rs` — orchestration (`check_flow`): whole-module pre-passes
  (global/borrow storage rules, borrowed-return reach seeding), the CFG
  engine run, cross-procedural borrowed-global write protection, and the
  `FlowFacts` product for the analysis layer.
- `cfg.rs` — the dataflow engine and the single flow authority: block
  worklist, successor edges per terminator, arm-binder seeding at
  `Switch` edges, and the three passes above.
- `moves.rs` — the `MoveState` lattice, the consume rules (what moves,
  what copies, what auto-clones), and the expression-level transfer
  functions the engine runs; also the drop classification rule
  (`classify`).
- `loans.rs` — NLL loans, provenance (`Origin`/`Provenance`), and the
  borrow conflict rules; borrows have no surface expression, they arise
  from `&`-typed parameters, borrow-containing bindings, arm binders
  over borrowed scrutinees, and `[&x]` captures.
- `liveness.rs` — borrower liveness: pre-order last-use positions decide
  where each loan ends; loop-carried uses extend to the loop's end.
- `grades.rs` — `GradeView`, the type-level ownership queries
  (`needs_drop`, `is_copy`, `is_object`, `contains_borrowed`,
  `is_cheap_clone`, `is_linear`, the symbol-level twins, and the
  syntactic `stores_borrow` walk); contract 2's authority. Every
  owned/object/borrowed classification in `flow/` and `lower/` routes
  through it — a raw catalog read of markers/grades outside this file
  is a bug (plan track 7.5).
- `place.rs` — `Place`: a root binding plus a field path, with
  prefix-based disjointness; `place_for_expr` is shared with lowering.
- `captures.rs` — closure captures: summaries, mode validation, escape
  checks, and the effects captures apply to the parent state.
- `drops.rs` — the drop vocabulary lowering consumes: `DropElaboration`
  (how a drop lowers) and `DropReason` (why it's scheduled there).
- `mir_annotate.rs` — contract 3's mechanism: mirrors recorded
  expression flags onto the typed-node copies embedded in checked MIR.
- `unsafe_gate.rs` — raw-pointer surface gating: outside core, types
  mentioning `RawPtr` (and inline IR) require a `// unsafe` line in the
  file.
- `errors.rs` — `OwnershipError`, the user-facing diagnostics; message
  text is pinned verbatim by the ported legacy corpus.

Tests live in `flow_tests.rs` and `flow_borrow_tests.rs`.
