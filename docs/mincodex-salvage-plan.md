# Mincodex critical-path execution plan

Status: preflight required

Architecture reference: [mincodex-target-architecture.md](mincodex-target-architecture.md)

## Path lock

This plan has one path:

```text
Baseline and feasibility
    -> Pattern decisions
    -> Phase-owned Core
    -> CFG ownership
```

We do not work on VM performance, formatting, highlighting, artifacts, or LSP
semantics while this plan is active. Those workstreams remain design targets
only. They require separate execution plans after CFG ownership lands.

We do not skip, parallelize, or reorder the four stages. A request for a later
stage stops at the first unfinished stage. It does not authorize a shortcut or
a temporary compatibility architecture.

## Pinned tree

Inventory revision: `85cf295d` (`Refactor unwind parking in MIR and runtime`)

Expected documentation-only working tree after this rewrite:

```text
M  docs/mincodex-salvage-plan.md
?? docs/mincodex-target-architecture.md
```

No source or generated change from an abandoned attempt may be present when
preflight starts.

The revision pin is refreshed before implementation if `HEAD` changes.

## Why this path is feasible

The current tree already contains the seams needed for this order:

1. Type checking has one diagnostic coverage owner in
   `types/exhaustiveness.rs` and one runtime pattern owner in MIR. They can be
   compared without changing Core or runtime production behavior.
2. Core already owns a checked tree and has phase marker types. Real phase
   transitions are absent, but pattern decisions can be attached to the
   existing nested match occurrence before `Nested -> Flat` is implemented.
3. MIR already grades local operands and has a shared CFG with unwind edges.
   Ownership cannot be completed yet because specialization and semantic
   operand decisions still live in `ProgramBuilder`/`FunctionBuilder`; that is
   exactly what phase-owned Core removes first.
4. The ownership regressions are already present, so the final cut has
   black-box runtime oracles on both VM and C paths.

No workstream outside this path is a prerequisite.

## Contracts that must be settled before source work

Previous attempts failed because these contracts were discovered during
cutover. They are now preflight requirements.

### Pattern product contract

`PatternResult` must contain both diagnostics and runtime facts from one matrix
recursion:

```text
PatternResult {
    report: MatchReport,
    tree: DecisionTree,
}
```

The tree must carry, before MIR sees it:

- source arm identity;
- every test and projection in source-preserving order;
- the checked occurrence type of every projected place;
- GADT arm refinement substitutions;
- binders and duplicate-binder ordering;
- whether a place is whole, destructured, or unbound;
- projection provenance through borrowed roots and heap objects;
- binding transfer relative to the scrutinee's ownership mode;
- guard continuation.

Important: ownership cannot be inferred from `Ty::Borrow` alone. A borrow-typed
slot inside an owned aggregate is owned by that aggregate and may transfer to
the arm. A borrowed scrutinee does not transfer it. The product must preserve
that distinction explicitly.

Catalog declaration types are not substitutes for checked occurrence types.
GADT payloads, associated projections, and desugared iterator payloads must use
the finalized type attached to that occurrence.

### Core phase contract

- `Core<Nested>` is emitted once by type finalization.
- `Nested -> Flat` consumes the stored decision tree.
- `Flat -> Closed` publishes one deterministic value/witness environment.
- `Closed -> Mono` is owned by `MonoPlanner`.
- `Core<Mono>` owns every executable instance and concrete edge.
- MIR lowering cannot access generic source-callable indexes or create an
  instance.

Optional semantic decision fields are temporary migration state. Each becomes
an ordinary node or mandatory field before `Core<Mono>` can lint.

### MonoPlanner contract

The planner reads checked Core and catalog facts. It owns:

- source callable indexing;
- instance canonicalization;
- roots and worklist;
- call, witness, conformance, handler, effect, and derived-body closure;
- exact closure environments;
- deterministic lowering order.

It does not allocate MIR ids, emit instructions, mutate MIR, or retry lowering.
Its differential product is a deterministic text form of instance keys, edges,
witnesses, handlers, effects, and derived bodies.

### Ownership contract

Current `record_flow`-style information has two lifecycle roles: pre-placement
input and post-placement verifier evidence. They must be separated before any
stream is collapsed.

Current forward ownership replay intentionally relies on separate release
planning for join equalization. Its entry states cannot be promoted as the new
production lattice. `OwnershipPlacement` must be introduced as a complete
lattice and compared from entry states outward.

The comparison order is fixed:

1. block entry initializedness;
2. loan state and borrow endings;
3. moves and replacements;
4. retains and displaced copies;
5. first-dead drops;
6. unwind-live sets and cleanup;
7. diagnostics;
8. finalized verifier evidence.

A later category is not debugged while an earlier category differs.

## Forbidden approaches

These approaches are known failures and may not be retried:

- writing a near-final quarry module before a current-tree seam is green;
- switching pattern control and leaf settlement in the same change;
- deriving pattern place types only from the catalog;
- deriving binding ownership only from `Ty::Borrow`;
- moving GADT refinement logic to MIR or reconstructing it there;
- unifying ownership sites and verifier events before separating their
  lifecycle roles;
- treating the current ownership replay's entry states as the final lattice;
- fixing a shared-analysis mismatch with a for-loop, match, handler, or
  writeback special case;
- updating MIR goldens before runtime and ownership gates pass;
- allowing formatter or unrelated rustfmt churn into a ticket;
- copying any quarry file or applying a quarry patch.

## Execution rules

### One numbered step at a time

A step is complete only when:

1. its exact gate passes;
2. intentional output is reviewed;
3. a rollback commit exists;
4. the status ledger records that commit.

The next step does not start in the same uncommitted working tree.

### Required pre-edit declaration

Before editing, state:

```text
Step:
Current owner:
Replacement owner:
Invariant moving now:
Allowed files:
Forbidden files:
Expected output change:
Gate:
Rollback commit:
```

Unknown fields stop the step.

### Stop conditions

Restore the rollback commit immediately if:

- a failure spreads outside predicted files or crates;
- a passing regression changes failure class;
- two fixes fail the same gate;
- a fix addresses a construct instead of the producing invariant;
- an absent prerequisite appears;
- unrelated formatting or generated churn appears;
- a quarry API begins driving current-tree design.

After restoring, update this plan before more source work.

### Quarry use

Quarry commits are evidence only. Allowed use is limited to focused path diffs,
invariants, and regression cases. Complete files, patches, and prerequisite
APIs are forbidden.

## Test environment

Every command runs from the current worktree:

```bash
export TALK_CORE_PATH="$PWD/core"
export TALK_STDLIB_PATH="$PWD/stdlib"
```

### Baseline gate

```bash
cargo fmt --all -- --check
cargo check --workspace
cargo test --workspace --no-fail-fast
cargo test --release --workspace --no-fail-fast
cargo check --target wasm32-unknown-unknown
```

Any existing failure is recorded verbatim and must remain unchanged until its
own approved fix. A feature step cannot silently absorb baseline cleanup.

### Pattern diagnostic gate

```bash
cargo test -p talk-front --test front_suite types_tests:: --no-fail-fast
cargo test -p talk-front --test front_suite core_tests:: --no-fail-fast
```

### Pattern runtime gate

```bash
cargo test --test talk_tests match --no-fail-fast
cargo test --test talk_tests run_projections_of_a_borrowed_scrutinee_keep_its_owner_alive -- --exact
cargo test --test talk_tests run_clone_of_an_element_settles_before_its_array_releases -- --exact
cargo test --test mir_goldens --no-fail-fast
```

### Core gate

```bash
cargo test -p talk-front --test front_suite types_tests:: --no-fail-fast
cargo test -p talk-front --test front_suite core_tests:: --no-fail-fast
cargo test --test mir_goldens --no-fail-fast
cargo test --test talk_tests run_executes_mut_arguments -- --exact
```

### Ownership gate

```bash
cargo test --lib compiling::mir::build:: --no-fail-fast
cargo test --test talk_tests parity_deinit_at_last_use -- --exact
cargo test --test talk_tests run_projections_of_a_borrowed_scrutinee_keep_its_owner_alive -- --exact
cargo test --test talk_tests run_clone_of_an_element_settles_before_its_array_releases -- --exact
cargo test --test talk_tests parity_suspend_cancel_unwinds -- --exact
cargo test --test talk_tests run_executes_mut_arguments -- --exact
cargo test --test mir_goldens --no-fail-fast
```

The module path in the unit command changes only after the approved
`build -> lower` rename step.

## Stage 0: baseline and feasibility

No source implementation begins until both steps land.

### B0 - Pin baseline

State: complete

Allowed files: this plan and an optional baseline report.

Actions:

1. Record `HEAD`, Rust/Cargo versions, and Talk binary revision.
2. Run the baseline gate twice.
3. Record pass/fail counts and every ignored test.
4. Hash MIR goldens, bootstrap manifests, and generated frontend artifacts.
5. Run `talk bootstrap --check` twice and record whether the tree is already a
   fixed point.
6. Verify the current-owner inventory below.

Output: documentation only.

### B1 - Prove the critical-path seams

State: complete

Allowed files: this plan and a feasibility report. No production source.

The report must name exact current symbols and data shapes for:

1. old pattern diagnostic input/output;
2. old runtime pattern control output;
3. old leaf binding/settlement output;
4. checked occurrence types and GADT refinements available before Core;
5. every published `Elaboration` and `TypeOutput` field and consumer;
6. current source callable index, demand key, worklist, and retry loop;
7. current ownership sites, events, sequence numbers, release plan, and
   verifier evidence;
8. the internal pre-final MIR seam where explicit ownership markers can live.

For each future differential, define a deterministic renderer and one existing
corpus command that exercises it. Confirm that no required input comes from a
workstream outside this path.

Gate: every item has one current owner, one replacement owner, and one oracle.
An unknown item blocks implementation and causes this plan to be revised.

## Current-owner inventory to verify in B1

### Pattern decisions

```text
Diagnostics:
  crates/talk-front/src/types/exhaustiveness.rs
  crates/talk-front/src/types/generate/mod.rs::check_matches

Runtime control and settlement:
  src/compiling/mir/build/mod.rs::compile_match
  src/compiling/mir/build/mod.rs::compile_pattern_test
  src/compiling/mir/build/mod.rs::settle_owned_match

Core occurrence:
  crates/talk-front/src/core/nodes.rs::ExprKind::Match
  crates/talk-front/src/core/build.rs
```

### Core and specialization

```text
Checked artifact:
  crates/talk-front/src/core/program.rs::CoreProgram
  crates/talk-front/src/core/build.rs

Current specialization/lowering owner:
  src/compiling/mir/build/mod.rs::ProgramBuilder
  src/compiling/mir/build/mod.rs::FunctionBuilder
  src/compiling/mir/build/entries.rs
  src/compiling/mir/build/glue.rs
```

Current facts:

- all four Core phase markers use the same file-tree representation;
- no real phase transition or `MonoPlanner` exists;
- Core is built from published elaboration tables after `check_types`;
- MIR owns source callable indexing, demand, worklist, effect retry, derived
  bodies, MIR ids, and instruction emission.

### CFG ownership

```text
src/compiling/mir/cfg.rs
src/compiling/mir/build/ownership.rs
src/compiling/mir/build/release.rs
src/compiling/mir/build/flow.rs
src/compiling/mir/build/verify.rs
```

Current facts:

- operands are structurally consume, borrow, or copy;
- the shared CFG includes normal and unwind edges;
- backward liveness exists;
- forward decisions and release planning are separate;
- lowering retains moved/scope/temp state, arm/loop snapshots, ownership sites,
  event sequence numbers, and flow events;
- verifier entry replay is a production input to release planning;
- explicit pre-final MIR ownership markers are absent.

## Stage 1: pattern decisions

No Core phase or ownership file changes during steps P1-P3.

### P1 - Add report-only patterns module

State: ready

Allowed files:

```text
crates/talk-front/src/types/patterns.rs
crates/talk-front/src/types/mod.rs
crates/talk-front/src/types/output.rs
crates/talk-front/src/types/generate/mod.rs
crates/talk-front/src/types/generate/artifacts.rs
crates/talk-front/src/types/generate/finalize.rs
crates/talk-front/src/types/generate/stmt.rs
pattern-specific frontend tests
```

Forbidden: Core and MIR files.

Implement only `MatchReport`. Collect pending match syntax before finalization,
run the new report owner over finalized occurrence facts, and retain its report
in `Elaboration`. Run old and new report owners in debug differential mode over
the complete frontend suite. Production remains old.

Gate: pattern diagnostic gate with zero differences in missing cases,
unreachable arms, ordering, or source ids.

### P2 - Add DecisionTree to the same recursion

State: blocked on P1

Allowed files: `patterns.rs`, `types/output.rs`, `types/generate/finalize.rs`,
and pattern tests only.

Extend the report recursion to return control flow and replace the retained
report with `PatternResult`. Do not add another recursive compiler. Add a
deterministic renderer and pin booleans, enums,
GADTs, tuples, records, structs, literals, or-patterns, guards, and source
ordering.

Gate: P1 differential remains exact; renderer snapshots pass.

### P3 - Complete leaf semantic facts

State: blocked on P2

Allowed files: `patterns.rs` and pattern tests only.

Add checked occurrence types, GADT refinement maps, binding transfer relative
to scrutinee ownership, duplicate-binder order, projection provenance,
unbound places, and destructured places.

Required focused fixtures:

- owned `Optional<&String>` payload transferred to a loop binder;
- borrowed enum matched after that binder becomes frame-owned;
- heap field projection;
- scalar field projection;
- GADT payload skolem refinement;
- associated-type payload;
- labeled pattern with two names at one place;
- or-pattern alternatives with equal binders.

Gate: tree snapshots prove every listed fact; P1 differential stays exact.

### P4 - Attach PatternResult to Core<Nested>

State: blocked on P3

Allowed files:

```text
crates/talk-front/src/core/nodes.rs
crates/talk-front/src/core/build.rs
crates/talk-front/src/core/facts.rs
core pattern tests
```

Core consumes and stores finalization's one retained pattern result. It does
not invoke a second compiler. MIR ignores it. Old production diagnostics and
runtime remain unchanged.

Gate: pattern diagnostic gate, Core serialization round trip, and unchanged MIR
goldens.

### P5 - Differential runtime realization

State: blocked on P4

Allowed files:

```text
src/compiling/mir/build/mod.rs
pattern differential tests
```

Substeps, each with its own rollback commit:

1. tests and branch topology;
2. projections;
3. bindings;
4. GADT refinements;
5. unbound/destructured settlement;
6. guards.

The old path remains production until all six normalized MIR products and
runtime outputs match. A substep does not modify the next category.

Gate after every substep: pattern runtime gate and ownership event
differential defined by B1. No golden update.

### P6 - Switch and delete old pattern owners

State: blocked on P5

Switch diagnostics and runtime together. Delete `exhaustiveness.rs`, syntax
pattern control in MIR, and the private differential. MIR may retain syntax
patterns only for source/debug metadata; no semantic query may inspect them.

Gate: pattern diagnostic gate, pattern runtime gate, ownership gate, then full
baseline gate. Review any intentional match-family golden change.

## Stage 2: phase-owned Core

No CFG ownership implementation changes during this stage.

### C1 - Emit Core<Nested> during finalization

State: blocked on P6

Current owner: `core/build.rs` consuming published elaboration.
Replacement owner: `types/generate/emit.rs` inside finalization.

Keep an internal old/new comparison. Clean files publish new Core only;
blocked files publish partial `NodeFacts`.

Gate: exact private tree comparison and Core gate.

### C2 - Make semantic occurrences mandatory and lint Nested

State: blocked on C1

Move one node family per rollback commit:

1. method/init resolution;
2. type application;
3. existential pack;
4. explicit and implicit clone;
5. witness arguments;
6. constructor/effect instantiation;
7. call operand modes.

Delete each occurrence table only after its last consumer moves. Nested lint
rejects missing facts and unzonked executable types.

Gate per family: Core gate and the family's focused regression.

### C3 - Implement Nested -> Flat -> Closed

State: blocked on C2

`Nested -> Flat` consumes `DecisionTree`. `Flat -> Closed` publishes one exact,
deterministic value/witness environment for nested functions and handlers.
Add phase-specific lints.

Gate: transition tests, closure environment equality tests, Core gate, and
unchanged runtime behavior.

### C4 - Add MonoPlanner in differential mode

State: blocked on C3

Extract source indexing and demand closure without moving MIR realization.
Compare the B1 planner renderer against current `ProgramBuilder` discovery.
Compare categories in order: roots, keys, call edges, witnesses,
conformances, handlers, static effects, derived bodies, closure environments,
then lowering order.

Gate: zero category differences on the Core gate and ownership regressions.

### C5 - Seal Core<Mono>

State: blocked on C4

Create the deterministic arena and annotate concrete edges and operand modes.
Mono lint proves transitive closure and exact witness/environment references.
The source callable index does not cross the planner seam.

Gate: Mono lint and C4 differential.

### C6 - Move MIR realization by family

State: blocked on C5

Move one family per rollback commit:

1. entries and globals;
2. calls and writeback;
3. constructors and flat matches;
4. closures;
5. effects and handlers;
6. derived bodies and glue;
7. teardown.

Introduce `MirLowerer`/`CoreLowerer` only as each family needs them. No family
may demand, retry, or use a source-body fallback.

Gate per family: Core gate, relevant runtime tests, and unchanged relevant MIR
goldens.

### C7 - Switch production and delete compatibility owners

State: blocked on C6

Production lowers only sealed `Core<Mono>`. Delete MIR demand, retry loops,
generic source indexes, old public occurrence decisions, and obsolete typed
program compatibility. Derive clean-file editor facts from Core. Rename
`build -> lower` only after semantic deletion is green.

Gate: Core gate, ownership gate, full baseline gate, and bootstrap fixed point.

## Stage 3: CFG ownership

### O1 - Separate pre-placement input from verifier evidence

State: blocked on C7

Introduce explicit internal ownership markers for definitions, reads, borrow
start/end, replacements, spends, and drops. Keep target-final MIR unchanged.
Separate production inputs from post-placement proof records. Do not collapse
streams yet.

Gate: structural marker verification, ownership gate, unchanged MIR goldens.

### O2 - Pin one backward liveness

State: blocked on O1

Move liveness inputs to explicit MIR markers and provenance. Compare source-use,
any-use, view birth, root lifetime, and copy settlement point by point. Remove
no forward or release owner yet.

Gate: zero liveness differential and ownership gate.

### O3 - Add complete OwnershipPlacement entry lattice

State: blocked on O2

Implement one `Cfg::forward` state containing initializedness, moves,
replacements, loans, displaced values, writeback obligations, and unwind-live
state. Compare block entries only. Existing production remains unchanged.

Gate: exact entry states across full workspace and ownership regressions.

### O4 - Compare and realize ownership decisions

State: blocked on O3

Move categories in the fixed ownership-contract order. Each category gets a
rollback commit and exact differential. No later category starts while an
earlier one differs.

Gate per category: ownership gate and unchanged production MIR.

### O5 - Switch production placement

State: blocked on O4

Use `OwnershipPlacement` for finalized MIR while retaining the old path as a
private debug comparison for this step only. Run VM/C parity and review every
intentional golden change by family.

Gate: ownership gate, full MIR golden suite, full baseline gate, and debug
verifier.

### O6 - Delete old ownership state and differential

State: blocked on O5

Delete separate release planning, ownership site/event/sequence streams,
ownership-only moved/scope/temp state, arm/loop snapshots, construct-specific
merge helpers, duplicate topology, comparison renderers, and feature flags.

Final shape:

- one shared CFG;
- one backward liveness;
- one forward `OwnershipPlacement`;
- one debug-only balance verifier.

Gate: ownership gate, full baseline gate, bootstrap fixed point, and no dead or
parallel owner found by repository search.

## Status ledger

Only the next unfinished step may be `ready`.

| Step | State | Green commit | Evidence |
| --- | --- | --- | --- |
| B0 | complete | `303381ca` | [`mincodex-baseline.md`](mincodex-baseline.md) |
| B1 | complete | `9f4b665c` | [`mincodex-feasibility.md`](mincodex-feasibility.md) |
| P1 | ready | - | feasibility and finalization handoff proved |
| P2-P6 | blocked | - | waits for numeric predecessor |
| C1-C7 | blocked | - | waits for pattern decisions and numeric predecessor |
| O1-O6 | blocked | - | waits for phase-owned Core and numeric predecessor |

## Completion of this plan

This plan is complete when O6 lands and a clean checkout passes:

```bash
export TALK_CORE_PATH="$PWD/core"
export TALK_STDLIB_PATH="$PWD/stdlib"

cargo fmt --all -- --check
cargo test --workspace --no-fail-fast
cargo test --release --workspace --no-fail-fast
cargo check --target wasm32-unknown-unknown
talk bootstrap --check
talk bootstrap --check
```

Also required:

- VM/C destruction and cancellation parity;
- reviewed MIR goldens;
- Core phase lints;
- no MIR demand or source-body fallback;
- no syntax pattern semantic consumer in MIR;
- no ownership differential or compatibility stream;
- no work from a deferred workstream mixed into the history.

After this plan completes, deferred workstreams receive new revision-pinned
plans. They do not begin automatically.
