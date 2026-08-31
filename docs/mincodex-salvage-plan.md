# Mincodex salvage plan

Status: approved

## Summary

Preserve the useful work from `mincodex` by reimplementing eight selected
workstreams on top of `main`:

1. regression specifications;
2. phase-owned Core;
3. CFG-based ownership analysis;
4. one LSP semantics module;
5. deterministic cross-session artifacts;
6. VM hot-path improvements;
7. Talk-owned formatting and highlighting;
8. one pattern decision module.

The source branch is a quarry, not a merge candidate. No commit from
`mincodex` is cherry-picked wholesale. Every workstream is rebuilt as a small,
reviewable sequence against the current tree, with its own behavior and
performance gates. Generated bootstrap artifacts and MIR goldens are always
regenerated from the resulting source; they are never copied from the branch.

Architectural decision records are not inputs or gates for this work. The
accepted target is the end state described here.

## Source quarry

The useful code is spread across these commits:

| Commit | Useful material |
| --- | --- |
| `29b9e79b` | Pattern decisions, initial CFG and ownership work, typed program move into `talk-front`, MIR builder split |
| `e2a151d5` | Talk formatter and highlighter, frontend schema work |
| `c27a327c` | Unified expansion/desugaring work that informs Core emission |
| `309fdfd6` | Ownership action stream and replay |
| `71a4eb44` | `typed_ast` to Core transition |
| `716b9d81` | Core and MIR lowering restructuring |
| `e99fb801` | Formatter/highlighter integration and ownership regressions |
| `16cc0c7f` | MIR validation ideas and VM implementation changes; do not copy the direct-MIR VM architecture |
| `03091232` | Flat syntax and formatter integration details |
| `51cf0739` | Generated frontend ABI views; use only where needed by formatting/highlighting |
| `d3ea4662` | Final Core shape, ownership passes, semantics module, deterministic images, VM optimizations, regression tests |
| `a2ff7f1f` | Generic-global mutable writeback regression |

The commits are not implementation units. They combine unrelated changes and
carry generated churn. Use path-level diffs and tests to understand behavior,
then write the smallest correct implementation for the current tree.

## End state

```text
Talk source
    -> parse, expansion, and name resolution
    -> type checking and finalization
    -> Core<Nested>
    -> Core<Flat>       (pattern decisions realized)
    -> Core<Closed>     (closure environments explicit)
    -> Core<Mono>       (all executable instances sealed)
    -> MIR lowering     (no typing or specialization decisions)
    -> CFG ownership placement
    -> finalized MIR
    -> existing target adapters
```

Supporting modules have these owners:

- `patterns` owns both exhaustiveness and decision-tree construction.
- `Core` owns every per-occurrence semantic decision needed downstream.
- `MonoPlanner` owns executable reachability and specialization closure.
- MIR lowering realizes Core; it cannot demand or infer new instances.
- `Cfg`, `Liveness`, and `OwnershipPlacement` own flow-derived ownership
  decisions.
- `Semantics` owns editor queries over syntax and checked facts.
- the syntax package owns formatting and highlighting policy.
- the artifact image module owns stable cross-session identity and wire
  determinism.
- the VM retains the current bytecode interface while adopting the independent
  hot-path improvements.

## Scope rules

1. Preserve current source behavior unless a regression specification in this
   plan deliberately requires a correction.
2. Do not import unrelated `mincodex` language changes.
3. Do not replace bytecode with executable MIR and do not make `talk-vm`
   depend on `talk-mir` as part of this plan.
4. Do not import the native stack-segment or unified `'suspend` runtime work.
5. Do not import record-row, overload, or effect-annotation semantic changes.
6. Do not complete the flat syntax arena migration unless a narrow typed view
   is required by formatting or highlighting.
7. Add no new third-party dependency. Existing workspace dependencies such as
   `bincode`, `serde`, `sha2`, and `rustc-hash` may be reused.
8. Keep every landing green. Temporary red tests may exist inside a local
   worktree, but not at a landed revision.
9. Set `TALK_CORE_PATH=$PWD/core` and `TALK_STDLIB_PATH=$PWD/stdlib` for every
   worktree test command. Never inherit those paths from another checkout.

## Workstream 1: regression specifications

### Goal

Retain the bugs discovered by the branch as permanent black-box
specifications, independent of the implementation that fixes them.

### Specifications to preserve

#### Last-use destruction

Source quarry:

- `tests/programs/deinit_at_last_use.tlk`
- `tests/parity/programs/deinit_at_last_use.stdout`

The specification must prove that values are destroyed after their last
source-visible use, including joins, nested aggregates, and loop exits. It
must run through both the VM and C adapters and compare the full destruction
order, not only the final result.

#### Borrowed projection lifetime

Source quarry:

- `run_projections_of_a_borrowed_scrutinee_keep_its_owner_alive` in
  `tests/talk_tests.rs`

The specification must keep the owner of a multi-level borrowed projection
alive until the projection's final use. It must exercise a reference-carrying
projection, not a scalar field that can be copied independently.

#### Clone settlement before source release

Source quarry:

- `run_clone_of_an_element_settles_before_its_array_releases` in
  `tests/talk_tests.rs`

The specification must prove that cloning an element from a borrowed array
settles the cloned result before releasing the source aggregate.

#### Suspension cancellation cleanup

Source quarry:

- `tests/programs/suspend_cancel_unwinds.tlk`
- `tests/parity/programs/suspend_cancel_unwinds.stdout`

Adapt the source to the current concurrency surface if necessary. Preserve the
semantic assertion: cancelling a one-shot resumption runs deinitializers for
every suspended frame exactly once on VM and C.

#### Borrowed static-call parameter

Source quarry:

- `tests/reference/strings/static_call_with_borrowed_parameter.tlk`
- its expected output

The specification must ensure that adaptation marks the argument occurrence,
not the static callee occurrence, when a static call receives a borrowed
parameter.

#### Generic global mutable writeback

Source quarry:

- the assertion added to `run_executes_mut_arguments` by `a2ff7f1f`

An inferred generic global may carry a type-application wrapper at use sites.
A mutating receiver call must still resolve to the underlying global place and
write back exactly once. The test must catch stale-buffer teardown or a double
free, not only check the visible count.

### Implementation method

1. Copy each source program or reconstruct the smallest current-syntax form.
2. Run it against unmodified `main` to classify it as already green or a
   genuine regression.
3. If already green, land the specification immediately.
4. If red, keep the test local and land it with the workstream that owns the
   fix:
   - projection, clone, and destruction tests with workstream 3;
   - static-call and generic-global tests with workstream 2;
   - cancellation cleanup with the smallest runtime fix required by the
     current runtime.
5. Add expected output only after independently checking the intended order.
6. Never weaken an assertion merely to preserve current output.

### Acceptance

- Every specification is present and enabled.
- VM and C agree for tests that exercise runtime cleanup.
- The tests fail when their corresponding branch fix is intentionally
  reverted.

## Workstream 2: phase-owned Core

### Goal

Make the checked program a phase-typed semantic tree. Every downstream typing,
adaptation, specialization, evidence, and closure decision is represented in
Core data. MIR lowering realizes those decisions and cannot recreate them.

### Target modules

```text
crates/talk-front/src/core/
    mod.rs
    nodes.rs
    program.rs
    facts.rs
    fold.rs

crates/talk-front/src/types/generate/emit.rs
src/compiling/mir/lower/
    mod.rs
    mono.rs
    ... construct-specific realizers
```

Delete after cutover:

```text
crates/talk-front/src/typed_ast/
src/compiling/typed_program.rs
src/compiling/typed_program/
```

### Core phases

#### `Core<Nested>`

Produced exactly once by type finalization. It contains checked nested
functions, typed binders and expressions, unresolved pattern control flow in
its checked form, and every per-occurrence semantic decision.

#### `Core<Flat>`

Produced by consuming pattern decisions. Pattern matching is explicit control
structure rather than a syntax pattern matrix. No later module may rerun
exhaustiveness or choose a match strategy.

#### `Core<Closed>`

Produced by closure analysis. Every nested function and handler carries its
exact value and witness environment in deterministic order. Closure emission
must not filter or rediscover captures.

#### `Core<Mono>`

Produced by whole-program specialization. It owns:

- executable roots;
- a deterministic arena of callable instances;
- handler instances;
- static-effect instances needed by the retained runtime;
- concrete call edges;
- concrete constructor and method targets;
- explicit witness arguments;
- per-argument operand modes;
- generated derived bodies.

### Node requirements

Core expressions must carry ordinary mandatory syntax for semantic operations,
not optional decision side fields. Include at least:

- `Method` with its selected resolution;
- `Init` with its selected resolution;
- `TyApp` with instantiation evidence;
- `Pack` with existential evidence;
- `Clone` for explicit and implicit clone operations;
- calls with witness arguments;
- concrete `Instance` edges in `Core<Mono>`;
- constructors with concrete type arguments;
- effect calls with their concrete instantiation;
- a match node containing the pattern module's decision product;
- argument operand modes: consume, borrow, or copy.

A consumer that needs a fact must obtain it from the node or a symbol-keyed
catalog fact. It must not consult a `NodeID -> decision` table or silently
rederive the fact.

### Finalization

1. Keep solver working state private to the type-checking session.
2. Complete all post-solve judgments before publishing Core.
3. Walk each unblocked syntax tree once to zonk types and emit
   `Core<Nested>`.
4. Emit editor `NodeFacts` from the same state for blocked files that cannot
   produce Core.
5. Derive facts for clean files by walking Core; do not publish a second copy
   from solver tables.
6. Keep `NodeID` only for source identity and editor lookup. Attach semantic
   call edges to Core occurrences, because synthesized wrapper and inner nodes
   can legitimately share a source id.

### Monomorphization

Introduce one `MonoPlanner` that owns:

- the generic source-callable index;
- the demand worklist;
- instance canonicalization;
- call, witness, conformance, and effect collection;
- target annotation;
- closure environment publication;
- the growing `Core<Mono>` arena.

Its query capability may read checked Core, the catalog, canonicalization,
conformance, and entry facts. It may not allocate MIR ids, emit instructions,
or mutate MIR.

The planner returns a sealed arena and deterministic lowering order. After it
returns:

- every concrete call edge names an instance in the arena;
- every required handler body is owned by the arena;
- every derived operation is an ordinary Core body;
- every closure environment is exact;
- MIR lowering has no `demand`, retry loop, source-body fallback, or
  specialization fallback.

### MIR realization

1. Introduce `MirLowerer` and `CoreLowerer` under
   `src/compiling/mir/lower/`.
2. Move construct-specific realization behind those modules without changing
   behavior.
3. Lower only `Core<Mono>`.
4. Require concrete edges and operand modes. Fail closed on a malformed Core
   value.
5. Keep ownership event publication temporarily if workstream 3 has not yet
   landed, but do not let it become a source of typing decisions.
6. Delete `ProgramBuilder` and `FunctionBuilder` only after all entry,
   closure, constructor, derived, handler, and teardown paths use the new
   lowerer.

### Lints

Run phase-specific lints at every transition:

- `Nested`: all mandatory semantic node fields are present and types are
  zonked;
- `Flat`: every match contains valid explicit control flow;
- `Closed`: closure and handler environments match their bodies;
- `Mono`: every concrete edge resolves, every argument has an operand mode,
  all witness blocks exist, and the arena is transitively closed.

Lint failures are compiler bugs with enough occurrence and symbol context to
locate the producer.

### Migration sequence

1. Add Core phase types and lints with no consumer cutover.
2. Teach finalization to emit Core while retaining the old artifact only
   inside the local stack.
3. Compare old and new outputs on the complete suite.
4. Move one MIR construct family at a time to Core consumption.
5. Seal `MonoPlanner` and remove MIR-side demand.
6. Switch all production entry points to Core.
7. Switch clean-file editor facts to derive from Core.
8. Delete the old typed program and every per-occurrence published table.
9. Rename remaining paths only after the ownership cut is complete; avoid a
   commit that is mostly rename plus semantic changes.

The old and new program artifacts must never both survive a landed revision as
public interfaces. The temporary comparison path stays private and is removed
in the same wave that production switches.

### Acceptance

- No `typed_ast` production module remains.
- No published `Elaboration` or equivalent per-occurrence decision bundle
  remains.
- `Core<Nested>`, `Core<Flat>`, `Core<Closed>`, and `Core<Mono>` each lint.
- MIR lowering cannot compile a generic source body or create a new instance.
- The generic source-callable index does not cross the planner seam.
- MIR goldens and runtime behavior stay pinned except where workstream 3
  deliberately changes drop placement.
- The static-call and generic-global regressions pass.
- Bootstrap reaches a fixed point.

## Workstream 3: CFG-based ownership analysis

### Goal

Replace ownership state threaded through lowering with one control-flow model,
one backward liveness computation, one forward ownership-placement
computation, and one debug proof over their published result.

### Target modules

```text
src/compiling/mir/cfg.rs
src/compiling/mir/lower/drops.rs
src/compiling/mir/lower/ownership.rs
src/compiling/mir/lower/escape.rs
src/compiling/mir/lower/verify.rs
```

### MIR prerequisites

Every local operand must be structurally graded as exactly one of:

- consume;
- borrow;
- copy.

MIR must also represent the ownership events required by analysis, including
explicit drop and end-borrow markers where their source ordering matters.
There is no neutral local operand whose mode is inferred during ownership
analysis.

### One CFG

`Cfg` owns:

- normal successors;
- unwind successors;
- predecessor edges with successor-slot positions;
- stable block indexing;
- forward fixpoint traversal;
- backward bitset traversal.

Register allocation, ownership, liveness, unwind handling, and structural
verification all use this model. No module keeps a second successor or
predecessor calculation.

### Backward liveness

Compute two related facets:

1. source-use liveness for donation, exclusivity, and displacement decisions;
2. any-use liveness for release placement.

Track projection provenance explicitly:

- reference-carrying projections keep their owner root alive;
- scalar copies do not keep an aggregate owner alive;
- raw pointers are not treated as managed views;
- instruction-defined views have definition points, so liveness does not bleed
  backward across loops or reassignment;
- a tracked copy keeps its source alive until the copy is defined.

### Forward ownership placement

`OwnershipPlacement` computes:

- initializedness at every entry;
- move and replacement state;
- borrow scopes and non-lexical loan death;
- retains and displaced copies;
- first-dead releases;
- unwind-live state;
- writeback obligations;
- join behavior through one state lattice.

The pass inserts or finalizes retains, drops, and end-borrow operations. A
construct-specific lowering function may publish operations but may not merge
ownership states itself.

### Escape analysis

Fold anchored-closure and escaping-reference propagation into one graph. Do
not maintain a separate taint stream in the lowering walk.

### Debug proof

Keep the balance verifier as an independent debug assertion over finalized
MIR. It proves the result; it does not recompute the production decision or
serve as a second planner.

### Deletions

Delete after cutover:

- lowering-side moved, temporary, scope, and uninitialized state used only for
  ownership decisions;
- per-arm and per-loop ownership snapshots;
- construct-specific merge functions;
- parallel ownership action, flow event, and sequence streams;
- separate release planning;
- duplicate CFG topology;
- MIR-side ownership re-derivation from types where Core already published the
  needed mode.

### Migration sequence

1. Add and pin the shared CFG, including unwind edges.
2. Convert existing analyses to the shared CFG without changing output.
3. Add operand grading and structural MIR verification.
4. Publish projection provenance and view birth points.
5. Implement backward liveness and compare its decisions with the current
   planner under a debug-only differential mode.
6. Implement forward ownership placement and compare entry states, drops,
   retains, and borrow endings.
7. Switch production to the new passes.
8. Run all ownership regressions and regenerate intentional MIR golden
   changes.
9. Delete the old state and event streams in the same landing.
10. Remove the differential path.

### Acceptance

- One CFG implementation serves all consumers.
- One backward and one forward production ownership pass remain.
- Lowering contains no arm/loop ownership-state merge code.
- Every ownership regression from workstream 1 passes.
- VM and C agree on destruction order and cancellation cleanup.
- The verifier passes in debug builds and is absent from release behavior.
- Twenty MIR family goldens cover calls, arrays, borrows, closures, drops,
  effects, enums, loops, globals, guards, writeback, protocols, strings,
  structs, and tuples.

## Workstream 4: one LSP semantics module

### Goal

Give editor features one deep query module over the workspace rather than
independent syntax walks and fact reconstruction.

### Target module

```text
src/analysis/semantics.rs
```

The module interface owns:

- document and file lookup;
- position to ancestor chain;
- first matching node traversal;
- node extent lookup;
- symbol declaration lookup;
- occurrence lookup;
- checked node type lookup;
- member resolution lookup;
- source callable lookup;
- callable signature rendering.

### Workspace data

A `Semantics` value borrows one analysis workspace. A `Document` groups the
file id, document id, resolved syntax tree, and text. Features must not
reassemble that tuple themselves.

For clean files, semantics reads `NodeFacts` derived from Core. For blocked
files, it reads the partial facts emitted by type finalization. The difference
is hidden behind the same query interface.

### Consolidations

1. `nodes_at`, `ancestor_at`, and `find_first` replace feature-specific
   position walks.
2. One occurrence walk serves occurrence-at, rename, and definition.
3. Hover and completion share source-callable lookup and signature rendering.
4. Code actions receive one `DiagnosticActionSite` instead of reconstructing
   diagnostic context in each action.
5. Editor workspace construction stops after checked Core. It must not
   monomorphize or lower the whole workspace on each edit.
6. Explicit CLI checking retains backend diagnostics through its own
   constructor.

### Migration sequence

1. Add `Semantics` as an internal module over existing workspace fields.
2. Move one read-only feature at a time: hover, definition, occurrences,
   rename, completion, then code actions.
3. After each move, delete the replaced feature-local traversal.
4. Switch semantics facts to Core-derived `NodeFacts` after workstream 2
   stabilizes.
5. Split editor and CLI workspace construction so only CLI checking reaches
   MIR.
6. Delete dead feature analysis structs and helpers.

### Required regressions

Preserve or add tests for:

- rename in extension heads;
- expansion-owned `self` spans;
- innermost node choice at shared span boundaries;
- protocol requirement declaration lookup;
- blocked-file hover and completion degradation;
- no MIR construction during ordinary editor analysis.

### Acceptance

- All editor features use `Semantics` for shared queries.
- There is one occurrence implementation.
- No ordinary editor request triggers monomorphization or MIR lowering.
- CLI checking still reports backend diagnostics.
- The migration removes more code than it adds outside tests.
- LSP latency does not regress on the existing benchmark corpus.

## Workstream 5: deterministic cross-session artifacts

### Goal

Make every serialized compiler product stable across hash insertion history,
cache round trips, process-local module numbering, and dependency reloads.

### Canonical hash serialization

Add:

```text
crates/talk-front/src/sorted.rs
    map
    set
```

The serde adapters sort keys or values on write and rebuild the original hash
container on read. Apply them to every serialized `FxHashMap` and
`FxHashSet`, including fields in:

- the type catalog;
- scopes and resolved names;
- type output and `NodeFacts`;
- Core workspace images;
- frame facts;
- module metadata;
- conformances;
- node metadata.

Do not replace runtime hash containers merely to obtain wire order. Wire
canonicalization belongs at the serialization seam.

### Stable module identity

Represent a module across sessions with `StableModuleId`, derived from its
canonical import name. Keep compact `ModuleId` values session-local.

Symbol serialization writes:

```text
(stable module identity, symbol kind, symbol index)
```

or an equivalent module-table index inside a framed image. It must never write
a process-local module integer as durable identity.

### Framed images

Add `src/compiling/image.rs` with this conceptual shape:

```text
Image {
    modules: [(StableModuleId, optional InterfaceFingerprint)],
    payload: bytes
}
```

Encoding:

1. Open an encode scope that records every session module id encountered.
2. Serialize the payload using module-table indexes.
3. Translate encountered ids to stable identities.
4. Attach the dependency interface fingerprint known by the writer.
5. Serialize the frame.

Decoding:

1. Decode the frame.
2. Resolve stable identities into this session's module ids.
3. Verify every recorded dependency fingerprint.
4. Refuse stale or malformed images.
5. Decode the payload under the module translation scope.

Use the same image module for Core artifacts, library products, and workspace
caches. Do not hand-build module translation independently at each caller.

### Catalog order

Where catalog position is identity, store entries in append order with a
rebuilt lookup index. A module slice is the exact range or ranges it appended.
Do not derive durable bytes from hash-table iteration.

### Versioning

Bump every affected cache or artifact format in the same landing as its wire
change. Old cache entries must fail closed and rebuild. Bootstrap artifacts
must be regenerated only after source and cache formats settle.

### Tests

1. Two maps and sets with opposite insertion histories serialize identically.
2. `encode(value) == encode(decode(encode(value)))` for every artifact family.
3. A cold compile and cache-hit compile produce byte-identical artifacts.
4. A changed dependency fingerprint rejects the cached image.
5. The same stable modules loaded in a different session order decode to the
   same symbols.
6. Malformed and trailing bytes fail closed.
7. Repeated package compilation in one process remains deterministic.

### Acceptance

- No serialized hash map or set relies on iteration order.
- No durable image stores a session module integer without translation.
- Every artifact is a fixed point of its cache round trip.
- Stale dependency interfaces invalidate their consumers.
- First cold run followed by a cache-hit run reports up to date and leaves
  artifact bytes unchanged.

## Workstream 6: VM hot-path improvements

### Goal

Port the independent VM throughput improvements while retaining the current
bytecode interface and observable VM behavior.

### Baseline first

Use the frontend VM benchmark and record:

- wall time;
- retired instructions when available;
- cycles when available;
- allocations;
- peak memory;
- executable image size;
- native and wasm execution time where runners exist.

Fix the benchmark harness before changing the VM. Pin the exact frontend
artifact and number of rounds through explicit environment variables or
arguments.

### Aggregate storage

Change flat aggregate slots from:

```text
Rc<Vec<Value>>
```

to:

```text
Rc<[Value]>
```

One allocation stores the reference count and adjacent values. Update
construction, transfer serialization, rendering, field reads, and tests.
Preserve copy-on-write value semantics.

### Field write

The current bytecode instruction may name distinct source and destination
registers. Implement both paths correctly:

- when `dest == rec`, take a mutable reference to the register's own `Rc` and
  call `Rc::make_mut` directly;
- when `dest != rec`, clone the source aggregate handle and perform normal
  copy-on-write into the destination.

Never clone the `Rc` before `make_mut` on the in-place path. That artificial
extra owner forces a full slot copy on every field write.

Add tests for:

- unique in-place write;
- shared in-place write copies once;
- distinct destination preserves the source;
- nested/spliced field writes;
- repeated writes do not allocate after uniqueness is established.

### Aggregate construction

Build aggregate slots directly from an exact-size operand iterator. Avoid an
intermediate vector of argument values. Keep a fast path for products whose
fields are plain declaration-order slots, while preserving the general
spliced-layout path.

### Allocation bounds cache

Add a one-entry cache to `Allocations`:

```text
(provenance id, allocation start, allocation end)
```

A load/store loop over one buffer then resolves its allocation record once.
Invalidate the cache whenever that provenance record dies. Reused spans get a
new provenance id and cannot reuse stale bounds.

Add tests for:

- cache hit on repeated interior accesses;
- invalidation on free;
- address reuse with a new id;
- stale pointer rejection;
- cross-allocation access rejection;
- static data behavior.

### Optimization discipline

Land each optimization separately and benchmark after each one. Revert an
optimization that does not improve the measured workload unless it produces a
clear independent simplification. Do not add unsafe indexing as part of this
workstream; consider it separately only if the safe changes leave a measured
hotspot.

### Acceptance

- All VM memory, object, IO, differential, and wasm tests pass.
- VM/C behavior remains identical.
- No resource-accounting behavior changes.
- Frontend benchmark retired instructions and wall time do not regress.
- The field-write benchmark demonstrates that repeated unique writes avoid
  repeated slot-vector copies.
- Release and debug test suites compile and pass.

## Workstream 7: Talk-owned formatting and highlighting

### Goal

Move language formatting and semantic highlighting policy into the syntax
package. Rust retains only transport, validation, and presentation adapters.

### Target files

```text
packages/syntax/src/format.tlk
packages/syntax/src/highlight.tlk
packages/syntax/tests/
crates/talk-front/src/parsing/highlighter.rs
src/compiling/frontend.rs
src/compiling/native_frontend.rs
```

Delete after cutover:

```text
crates/talk-front/src/parsing/formatter.rs
```

### Formatter

Port the current formatter behavior around one document algebra implemented in
Talk. It must own:

- groups and indentation;
- line and soft-line decisions;
- source-width constraints;
- comment attachment and comment cursors;
- blank-line preservation;
- operator precedence and parentheses;
- declaration and expression formatting;
- macro, quote, wrapper, ownership-mode, label, static-generic, and effect
  syntax.

Export one operation equivalent to:

```text
format_source(source, width) -> String
```

Both native and VM frontend execution call that same operation. Rust test
helpers may adapt the export but may not contain a second formatter.

### Highlighter

Talk owns lexical and AST-semantic classification and returns typed highlight
records. Rust owns only:

- ABI validation;
- DTO conversion where unavoidable;
- HTML or protocol-specific rendering.

The frontend schema must keep parse and highlight products reachable. Add only
the narrow typed ABI records required for this interface; do not make the
complete flat-arena migration a prerequisite.

### Requirements and diagnostics callers

Any caller currently reformatting syntax to create diagnostics must instead
use the written source span or the formatter export. Do not preserve a hidden
Rust formatting path for one caller.

### Migration sequence

1. Pin every existing Rust formatter case and add package-level syntax tests.
2. Implement the Talk document algebra and primitive rendering tests.
3. Port syntax families incrementally until the existing corpus is identical.
4. Add native/VM formatter differential tests.
5. Switch production formatting to the frontend export.
6. Delete the Rust formatter and its private helpers.
7. Implement Talk highlighting and typed result records.
8. Add native/VM highlight differential tests.
9. Reduce Rust highlighting to validation and rendering.
10. Regenerate the frontend ABI, native artifact, bytecode seed, and website
    assets; verify a bootstrap fixed point.

### Required tests

- all existing formatter tests;
- core and examples formatting idempotence;
- package syntax tests for groups, joins, lines, comments, output, and
  rendering;
- comments attached to roots, blocks, calls, chains, and long lines;
- wrapper and macro stability;
- quoted identifiers;
- ownership parameter modes and argument markers;
- callable labels;
- static generics;
- extension heads;
- force unwrap and unreachable syntax;
- native/VM byte-identical formatting;
- native/VM identical highlight token streams.

### Acceptance

- `formatter.rs` is deleted.
- There is one formatting policy, in Talk.
- There is one highlighting policy, in Talk.
- Rust highlighter code is a thin adapter and renderer.
- Existing formatting output is preserved unless an individual test records an
  intentional correction.
- Formatting core and examples twice is byte-identical to formatting once.
- Bootstrap is a fixed point.

## Workstream 8: one pattern decision module

### Goal

Use one matrix compiler for exhaustiveness, unreachable-arm reporting, and
runtime match control flow.

### Target module

```text
crates/talk-front/src/types/patterns.rs
```

Delete after cutover:

```text
crates/talk-front/src/types/exhaustiveness.rs
```

and any independent MIR match compiler that chooses control flow from syntax
patterns.

### Interface

The module accepts a checked pattern matrix, scrutinee types, source arm
identity, and catalog queries. It returns:

```text
PatternResult {
    tree: DecisionTree,
    report: MatchReport,
}
```

`MatchReport` contains missing cases and unreachable arms. `DecisionTree`
contains the explicit tests, projections, binders, guards, and leaves needed
by Core flattening and MIR realization.

This is one module with one recursive algorithm. Exhaustiveness must not run a
parallel recursion that can disagree with lowering.

### Semantic cases

Handle and pin:

- enums and nested payloads;
- tuples and records;
- GADT-impossible variants;
- binders and wildcards;
- or-patterns with equivalent binders and refinements;
- guards;
- integer, string, byte, character, and boolean literals;
- borrowed scrutinees and reference-carrying payloads;
- labeled payloads and duplicate binders;
- unreachable arms and missing cases.

String and integer catalog values may require equality tests in source order
rather than discriminant switches. Preserve source arm order where tests can
overlap or equality is user-defined.

A borrow-typed component of an owned aggregate is not automatically an
independent owning value. Pattern binding modes and projection provenance must
be explicit in the decision tree so workstream 3 can keep the correct owner
alive.

When a labeled pattern introduces two names at one place, define one stable
ownership rule and pin it; do not let traversal order choose accidentally.

### Core integration

1. During finalization, compile each checked match matrix once.
2. Store the decision product on the `Core<Nested>` match occurrence.
3. `Nested -> Flat` consumes the tree and emits explicit match control flow.
4. MIR realizes the flat form. It does not inspect source patterns or rerun
   usefulness.
5. Editor diagnostics read `MatchReport` or Core-derived facts.

### Migration sequence

1. Build the new module beside the current exhaustiveness checker.
2. Differentially compare missing cases and unreachable arms over the entire
   frontend suite.
3. Add decision-tree rendering for test diagnostics only.
4. Compare runtime behavior by realizing the new tree while retaining the old
   checker.
5. Switch diagnostics and Core to the new result together.
6. Delete old exhaustiveness and independent MIR pattern compilation.
7. Remove the differential renderer if it has no production or debugging use.

### Acceptance

- One recursive pattern algorithm remains.
- Every match Core node carries its checked decision product.
- Exhaustiveness and runtime lowering cannot disagree by construction.
- Existing GADT, enum, tuple, record, literal, guard, borrow, and or-pattern
  tests pass.
- The pattern-specific ownership regressions pass under workstream 3.

## Execution order

The implementation order minimizes throwaway adapters and keeps each landing
reviewable.

### Wave 0: preserve and measure

1. Create a permanent archive ref for `mincodex`.
2. Record baseline test counts, ignored tests, bootstrap hashes, MIR golden
   hashes, VM benchmark data, LSP latency, and source line counts.
3. Build a path-level quarry index for all eight workstreams.
4. Confirm the full baseline with explicit worktree-local core and stdlib
   paths.

Gate: no source behavior change.

### Wave 1: regression inventory

Classify every workstream 1 test against `main`. Land already-green tests.
Assign each red test to its owning later wave.

Gate: all landed tests green; every deferred local red test has one named
owner in this plan.

### Wave 2: VM hot paths

Execute workstream 6 in four narrow lands:

1. benchmark harness;
2. aggregate storage and construction;
3. field-write copy-on-write correction;
4. allocation bounds cache.

Gate: workspace tests, VM/C differential, wasm checks, and before/after
benchmark report.

### Wave 3: pattern decisions

Execute workstream 8 while the current typed tree still exists. Store the new
result in the existing match representation in a way that can move unchanged
into Core.

Gate: diagnostic differential, runtime differential, frontend suite, MIR
match goldens.

### Wave 4: Talk formatter and highlighter

Execute workstream 7 before the major Core cut so formatter and highlighting
no longer add Rust AST consumers that must migrate.

Gate: formatter corpus, syntax-package tests, native/VM differential,
bootstrap fixed point.

### Wave 5: phase-owned Core

Execute workstream 2. Preserve current ownership analysis during the initial
cut, but publish graded operands and exact semantic facts required by the next
wave.

Gate: Core lints, frontend tests, workspace tests, MIR goldens, runtime
parity, static-call and generic-global regressions, bootstrap fixed point.

### Wave 6: CFG ownership

Execute workstream 3 and land the destruction, projection, clone, and
cancellation regressions.

Gate: ownership differential removed, all ownership tests, VM/C parity,
debug verifier, MIR goldens, bootstrap fixed point.

### Wave 7: deterministic artifacts

Execute workstream 5 after Core and catalog wire shapes have settled.

Gate: fixed-point bytes for every artifact, cold/cache-hit equality, stale
fingerprint rejection, package determinism, bootstrap fixed point.

### Wave 8: LSP semantics

Execute workstream 4 over the final Core and `NodeFacts` shape.

Gate: analysis and LSP tests, blocked-file behavior, rename regressions, no MIR
on editor path, latency benchmark.

### Wave 9: integrated closure

1. Run every gate below from a clean checkout and cold cache.
2. Remove temporary differential paths, compatibility artifacts, dead feature
   flags, and stale module summaries.
3. Regenerate bootstrap and website assets once.
4. Measure final production, test, generated, and documentation line counts
   separately.
5. Verify every deletion criterion in the completion checklist.

## Standard gate for every wave

Run from the wave's worktree:

```bash
export TALK_CORE_PATH="$PWD/core"
export TALK_STDLIB_PATH="$PWD/stdlib"

cargo fmt --all -- --check
cargo test --workspace
```

Add the wave-specific gates below where applicable:

```bash
cargo test --release --workspace
cargo check --target wasm32-unknown-unknown

talk bootstrap
talk bootstrap --check
```

Also run:

- all syntax package tests from `packages/syntax`;
- VM/C differential tests;
- MIR goldens;
- end-to-end reference tests with full checking enabled;
- frontend native/VM differential tests;
- the frontend VM benchmark;
- LSP latency tests for editor waves.

A bootstrap regeneration is complete only when a second `talk bootstrap
--check` reports no change.

## Commit and review discipline

1. One commit has one owner and one reason.
2. Separate mechanical moves from semantic rewrites.
3. Do not combine generated artifacts with unrelated source changes.
4. Do not delete documentation and restore it later.
5. Keep branch quarry hashes in commit messages for provenance, but explain the
   new implementation rather than claiming a cherry-pick.
6. Every deletion commit names the replacement module and its passing tests.
7. Every wire change names its format bump and invalidation behavior.
8. Every performance commit includes before/after measurements.
9. Every intentional golden change is reviewed as behavior, not hidden in a
   bulk regeneration.
10. Do not land a compatibility layer without naming the wave that deletes it.

## Risks and controls

### Missing Core facts

Risk: a solver table is deleted before every clean and blocked-file consumer
has a replacement.

Control: inventory every published table, classify it as occurrence data,
symbol data, or solver-private state, and require a compile-time consumer
migration plus a Core lint before deletion.

### Duplicate Core occurrence ids

Risk: synthesized wrappers and inner expressions can share `NodeID`, causing a
call edge attached through an id map to hit the wrong occurrence.

Control: semantic edges live on Core occurrences. `NodeID` is source identity,
not semantic-instance identity.

### Specialization closure gaps

Risk: derived calls, handler bodies, local recursion, deinit hooks, or witness
requirements are discovered during MIR lowering.

Control: `MonoPlanner` owns a closed worklist and `Core<Mono>` lint rejects any
edge outside its arena. MIR has no demand operation.

### Closure environment disagreement

Risk: closure construction and function prologues independently choose capture
order.

Control: one `ClosureEnvironment` product drives both sides and includes value
and witness captures.

### Ownership aliasing errors

Risk: borrowed projections release their owners too early, while scalar
projections retain owners too long.

Control: explicit projection provenance, view birth points, separate
source-use and any-use liveness, and the workstream 1 regressions.

### Formatter bootstrap cycle

Risk: a broken formatter changes the self-hosted frontend source and makes its
own artifact hard to rebuild.

Control: retain the previous bootstrap seed during development, test native
and VM exports independently, and replace checked-in artifacts only after all
formatter tests and idempotence checks pass.

### Artifact nondeterminism

Risk: one unannotated hash field or session id keeps cache bytes unstable.

Control: enumerate every serialized container and module id, add a fixed-point
test per artifact family, and make the integrated cold/cache-hit gate compare
bytes.

### VM copy-on-write regression

Risk: optimizing in-place field updates mutates an aliased aggregate or changes
`dest != rec` behavior.

Control: preserve separate in-place and copy paths and test unique, shared, and
distinct-destination cases with allocation counts.

### Editor partial programs

Risk: requiring complete Core removes hover or completion from files with type
errors.

Control: finalization emits partial `NodeFacts` for blocked files and
`Semantics` hides whether facts came from Core or partial checking.

### Scope expansion

Risk: quarry code pulls in unrelated runtime, VM architecture, or language
semantics.

Control: enforce the scope rules at review. A needed change outside the eight
workstreams requires an explicit amendment to this plan before implementation.

## Completion checklist

### Regression specifications

- [x] Last-use destruction is pinned on VM and C.
- [x] Borrowed projection owner lifetime is pinned.
- [x] Clone settlement before source release is pinned.
- [x] Suspension cancellation cleanup is pinned on VM and C.
- [x] Borrowed static-call adaptation is pinned.
- [x] Generic global mutable writeback is pinned.

### Phase-owned Core

- [ ] Finalization emits `Core<Nested>` once.
- [ ] `Nested -> Flat -> Closed -> Mono` transitions lint.
- [ ] Every required per-occurrence semantic decision is a Core node or field.
- [ ] `MonoPlanner` returns a sealed deterministic arena.
- [ ] MIR lowering has no typing, specialization, or demand fallback.
- [ ] Old typed program modules and published decision tables are deleted.

### CFG ownership

- [x] All local operands are consume, borrow, or copy.
- [x] One CFG serves all analyses.
- [x] One backward liveness pass remains.
- [ ] One forward ownership-placement pass remains.
- [ ] Construct-specific ownership merges and parallel event streams are
      deleted.
- [x] Debug balance verification passes.

### LSP semantics

- [ ] Shared editor queries live in `Semantics`.
- [ ] One occurrence walk serves definition, rename, and occurrences.
- [ ] Hover and completion share callable rendering.
- [ ] Editor analysis stops at checked Core.
- [ ] CLI checking retains backend diagnostics.

### Deterministic artifacts

- [ ] Every serialized hash container has canonical wire order.
- [ ] Stable module identity replaces durable session numbering.
- [ ] Core, library, and workspace products use framed images.
- [ ] Dependency fingerprints reject stale products.
- [ ] Every artifact is a byte fixed point of its round trip.

### VM performance

- [ ] Benchmark harness is pinned and repeatable.
- [ ] Aggregates use `Rc<[Value]>`.
- [ ] Unique in-place field writes do not force a copy.
- [ ] Distinct-destination field writes preserve source semantics.
- [ ] Allocation bounds cache is correct under free and address reuse.
- [ ] Before/after measurements show no regression.

### Talk formatter and highlighter

- [ ] Formatting policy lives in `packages/syntax`.
- [ ] Highlight classification lives in `packages/syntax`.
- [ ] Rust formatter is deleted.
- [ ] Rust highlighter is a thin adapter and renderer.
- [ ] Native and VM outputs agree.
- [ ] Core and examples formatting is idempotent.

### Pattern decisions

- [ ] One pattern matrix recursion remains.
- [ ] It produces both `DecisionTree` and `MatchReport`.
- [ ] Core carries the checked decision product.
- [ ] MIR does not inspect source patterns.
- [ ] Exhaustiveness and runtime control flow cannot diverge.

### Final integration

- [ ] Full workspace debug and release tests pass.
- [ ] VM/C differential passes.
- [ ] Wasm check passes.
- [ ] MIR goldens are reviewed and green.
- [ ] Syntax package tests pass.
- [ ] LSP tests and latency gates pass.
- [ ] Frontend VM benchmark does not regress.
- [ ] Bootstrap is a fixed point.
- [ ] No temporary comparison path or compatibility artifact remains.
