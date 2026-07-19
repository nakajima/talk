# Backend feature-parity plan

Status: proposed execution plan (2026-07-14)

Semantic authority: [ADR 0032](adr/0032-single-artifact-ownership-and-lowering-pipeline.md)

Implementation status: [Backend implementation status](backend-status.md)

Parity accounting: [Backend parity ledger](backend-parity-ledger.md)

E1 design: [E1 scalar execution plan](e1-scalar-execution-plan.md)

E1 runtime audit: [E1 talk-runtime reuse audit](e1-talk-runtime-reuse-audit.md)

Accepted R1 design:
[ADR 0033](adr/0033-managed-storage-heap-regions-and-ffi-lifetimes.md)

Historical baseline: `pre-backend-reset-2026-07-13` at `96249e71`

## Goal

Restore the user-visible language and tool capabilities of the last green
pre-reset compiler through the canonical pipeline:

```text
ParsedProgram
  -> TypedProgram
  -> CheckedMir
  -> TalkIrModule
  -> bytecode reference backend
```

The plan preserves the phase ownership, cross-artifact laws, and G0-G5 gates
from ADR 0032. It does not restore the deleted flow, lowering, lambda-G, VM
scheduler, or evaluator interfaces.

Feature parity and backend breadth are different milestones:

- **Feature parity** means every required baseline behavior executes through one
  audited reference backend, initially bytecode.
- **Backend breadth** means additional Talk IR adapters implement the same rows:
  WebAssembly, C translation, Cranelift, and LLVM.

A bytecode adapter is enough to recover the old compiler's language and tool
capability. The additional adapters prove and extend Talk IR's target
neutrality; they do not hold the parity milestone hostage.

## Parity charter

A behavior from the baseline is classified as one of:

1. **Required parity** - the new pipeline must preserve its observable source
   semantics.
2. **Deliberate semantic change** - ADR 0032 or a later accepted ADR defines
   different behavior.
3. **Unsafe behavior replaced by rejection** - the baseline accepted a program
   that violated the adopted ownership, borrow, cleanup, or control-linearity
   rules. Parity requires a source diagnostic or a safe implementation, never
   restoration of the bug.
4. **Old implementation-only test** - the test asserted flow annotations,
   lambda-G, scheduler, evaluator, or bytecode internals that are not part of
   the new interfaces.
5. **Post-parity expansion** - useful behavior that the baseline itself did not
   provide, including independent Wasm, C, Cranelift, and LLVM adapters.

Parity is measured by required behavior rows, not by the total number of tests.
Frontend tests remain necessary but cannot establish compiler-pipeline parity
while later phases are absent.

## Observable parity

A required behavior reaches parity only when all applicable observations agree:

- frontend acceptance or rejection;
- result value;
- stdout and stderr;
- source diagnostic kind and primary origin;
- deterministic cleanup and deinitialization order;
- allocation and resource balance;
- external IO behavior under the same host adapter;
- package, CLI, REPL, or embedding behavior when the feature is exposed there.

Expected output and diagnostics are frozen from reviewed baseline behavior.
Known baseline memory-safety bugs are not semantic oracles.

## Architectural constraints

The following constraints apply to every phase below:

- Exactly one semantic artifact crosses each phase seam.
- MIR generation consumes only validated `TypedProgram`.
- Talk IR lowering consumes only verified `CheckedMir`.
- Target adapters consume only verified `TalkIrModule` and explicit target
  configuration.
- No persistent semantic side table, source-AST fallback, or old-artifact query
  may fill a contract gap.
- Type checking selects Copy, Move, Borrow, clone, witness, and handler facts.
- MIR owns ownership, loans, cleanup, pattern CFG, and source diagnostics.
- The lowerer owns reachability, monomorphization, witness materialization,
  closure conversion, generated glue, and target-neutral representation.
- Backends preserve explicit Talk IR semantics and do not reconstruct source
  ownership.
- Unsupported rows fail before partial lowering.
- No second evaluator is introduced.
- `talk-runtime` remains quarantined until an explicit audit accepts a reusable
  subset. Its old continuation and object-region architecture is not authority.
- Uniform reference counting remains rejected. Type-specific CoW and explicit
  generated cleanup remain permitted.

## Why the previous cadence was insufficient

ADR 0032 established the correct seams, but its original feature cadence was too
coarse for parity delivery.

### No explicit baseline inventory

The old plan named broad capabilities without mapping the archived source tests,
complete programs, commands, and embeddings to those capabilities. A green
artifact suite therefore did not answer which user behaviors had returned.

### Slices were too wide

For example, `aggregates/match` combines anonymous type identity, layout, enum
tags, projections, pattern decision trees, borrowed versus consuming payloads,
cleanup, generated glue, and backend representation. `Effects` similarly
combines behavior verification, dynamic routing, continuation representation,
discontinue cleanup, generic instantiation, and captures.

### Execution was deferred too long

A verifier can prove an IR internally consistent while a real backend exposes a
bad calling convention, unusable block parameter shape, target-specific
intrinsic, or incomplete import model. G5 must begin as soon as a useful common
subset is explicit.

### Runtime semantics were under-specified

Heap cycles, CoW buffers, element finalization, deinit ordering, continuation
cleanup, host IO, and bytecode validation were bundled in the old runtime. The
new pipeline must assign those behaviors to Talk IR, generated glue, or a target
module deliberately.

### Test counts substituted for behavior coverage

The canonical frontend now has more tests than the reset baseline, but broad
execution remains absent. The parity ledger therefore tracks behavior rows and
G0-G5 state rather than a percentage based on test count.

## Planning and integration model

### Slice-local contract audit

Do not add another speculative all-feature contract skeleton. Before each slice,
inspect whether the current artifact can represent that slice without guessing.
Known likely contract questions include:

- anonymous tuple and closed-record identities and projections;
- existential pack/unpack and witness payloads;
- target-neutral intrinsic identities and exact scalar semantics;
- global initialization and linked-module ordering;
- managed storage and heap-object operations;
- generated clone, destroy, and deinit identity;
- the input and output shape of Talk IR linking.

When a real contract gap is found, update in one coordinated stack:

1. ADR 0032;
2. `docs/stage-0-contract-types.md`;
3. Rust contract types;
4. validators and verifiers;
5. artifact printers;
6. negative tests;
7. `docs/backend-status.md`;
8. `docs/backend-parity-ledger.md`.

### Vertical slices

Each implementation slice crosses all applicable modules:

```text
source producer
  -> TypedProgram validation
  -> MIR fixture, producer, diagnostics, and verification
  -> Talk IR fixture, lowering, and verification
  -> backend adapter and runtime
  -> black-box behavior and resource checks
```

Fixture-only work may be one slice ahead, but production input remains rejected
until the real handshake lands.

### Definition of done for one row

Every supported row includes:

1. a source producer test;
2. a negative source recovery test where applicable;
3. a validator-approved MIR fixture;
4. a malformed or unsupported MIR verifier test;
5. a real TypedProgram-to-MIR handshake;
6. a validator-approved Talk IR fixture;
7. a malformed or unsupported Talk IR verifier test;
8. a real MIR-to-Talk-IR handshake;
9. an assertion naming the relevant identity, shape, ordering, provenance, or
   erasure law;
10. a bytecode black-box result, output, or diagnostic test;
11. an allocation or resource-balance assertion where applicable;
12. ledger updates;
13. G4 from rebased `bigdiff`;
14. G5 for every backend claiming the row.

## Phase P0 - Freeze the parity inventory

The parity ledger is the first deliverable and remains live throughout the
work.

For each row it records:

```text
ID
classification
baseline fixtures
observable oracle
TypedProgram requirements
MIR requirements
Talk IR requirements
runtime and tool requirements
current phase support
G0-G5 state
blocker
integrating commit
```

Inputs are:

- tag `pre-backend-reset-2026-07-13`;
- `docs/parity-test-audit.md`;
- the 16 complete programs in `tests/programs`;
- archived VM, flow, and lowering suites;
- examples, package fixtures, and embedding tests;
- `talk-syntax` and `talispk`;
- ADR 0032's deliberate changes and conservative v1 restrictions.

`docs/parity-test-audit.md` audited an earlier backend rewrite. It is evidence,
not proof that the post-reset pipeline implements those rows.

### P0 exit

- Every archived behavior is assigned to a parity row or an explicit
  non-required disposition.
- Every complete program has frozen expected output, exit behavior, and resource
  expectations.
- No archived test is silently omitted because its old module was deleted.

## Phase E1 - Executable scalar core

### Capability

- Unit, Bool, Int, and Float from the real producer;
- Byte operations in validated fixtures until managed memory provides a real
  Byte producer;
- arithmetic and comparisons through checked trusted intrinsics;
- branches, literal switches, loops, and unreachable;
- local direct calls;
- consumed scalar parameters and results.

Character is a borrowed grapheme view under ADR 0012 and is not an E1 scalar.

### Frontend and MIR

- Canonicalize approved trusted inline IR into explicit checked scalar
  intrinsics before the TypedProgram seam.
- Specify integer width, overflow, division, float, conversion, and comparison
  semantics.
- Diagnose out-of-range Int literals before MIR.
- Preserve source argument order, exact callable identity, and source origins.

### Talk IR

- Replace the empty intrinsic vocabulary with the exact target-neutral scalar
  operation set.
- Verify operation arity and operand/result types.
- Reject unknown or target-specific operations.

### Bytecode reference backend

- Audit `talk-runtime` before reuse.
- Add one adapter from verified Talk IR to validated bytecode.
- Keep register selection, bytecode encoding, and interpreter details behind
  that target module's interface.
- Do not restore lambda-G or capability-passing CPS.
- Track result values, output, allocations, and runtime failures from the first
  executable fixture.

### E1 black-box fixtures

- constant result;
- trusted direct scalar arithmetic;
- comparison branch using a trusted direct helper;
- loop;
- local call;
- recursive scalar call;
- malformed Talk IR and malformed bytecode rejection.

### E1 exit

The scalar common subset passes G0-G5. `talk run` is restored for the supported
subset and reports an explicit unsupported phase for every later row. Normal
operator syntax remains fail-closed until L1 publishes and materializes the
selected witness; E1 may not search for that witness downstream.

## Phase E2 - Module linking, globals, and external supply

### Capability

- source module imports;
- bodyless external callables;
- public and stable internal exports;
- globals and deterministic initialization;
- exact module/export/signature supply.

### Work

- Add a Talk IR linker module that combines verified Talk IR modules into one
  verified Talk IR module. It does not introduce another semantic IR.
- Require exactly one compatible supplier for every reachable source-backed
  import.
- Reject missing, duplicate, and signature-incompatible suppliers.
- Preserve source declaration order within a module; order initializer-reachable
  dependencies before consumers with deterministic cycle diagnostics.
- Preserve stable generated and private witness link names.

The exact-supplier scalar linker, negative supplier/signature fixtures, output
re-verification, real supplier/consumer source-module handshake, generated
private initializer suppliers, linked scalar globals, cycle rejection, and
validated bytecode execution are integrated. Package graph production and exact
external global imports remain.

### E2 exit fixtures

- cross-module scalar call;
- generated dependency callable;
- missing supplier;
- duplicate supplier;
- signature mismatch;
- global initialized exactly once.

## Phase L1 - Monomorphization and static witness dispatch

### Capability

- generic scalar functions;
- recursive specializations;
- multiple concrete instantiations;
- statically selected protocol requirements;
- associated-type substitution;
- default requirements;
- operator witnesses.

### Lowerer work

Use a reachability worklist keyed by canonical callable identity, exact type
substitution, and selected witnesses. A selected imported callable whose entire
exported implementation is one validated scalar intrinsic is materialized in
MIR before this worklist and needs no external specialization. The implementation
must:

- produce one stable specialization per key;
- terminate recursive specialization;
- preserve the exact specialized call signature;
- materialize selected witnesses without conformance search;
- reject executable types that remain open or unresolved.

### L1 exit fixtures

- generic identity at Int and Bool;
- generic recursion;
- arithmetic through selected operator witnesses;
- protocol default;
- conditional conformance with satisfied and unsatisfied contexts;
- specialization identity collision rejection.

## Phase L2 - Copy aggregates and pattern CFG

The phase is divided so representation, pattern semantics, and target layout do
not land as one opaque `aggregates/match` change.

### L2a - Representation

- tuples and closed records;
- value structs;
- payload-free enums;
- payload enums;
- construction, projection, and discriminant;
- target-neutral field order and variant tags.

Resolve anonymous tuple and record identity before implementation. Do not encode
source labels where a canonical structural identity is required.

### L2b - Pattern compilation in MIR

- literal patterns;
- tuple and record patterns;
- variant patterns;
- wildcard and default;
- or-patterns;
- nested patterns;
- guards where supported;
- source-order evaluation.

Source patterns end in MIR. Talk IR receives only explicit CFG, discriminants,
projections, and values.

### L2c - Backend representation

- value aggregate storage;
- aggregate parameters and returns;
- enum tag and payload access;
- no managed heap semantics yet.

### L2 exit fixtures

- `tuple_access.tlk`;
- record construction and assignment;
- nested enum patterns;
- wildcard and or-patterns;
- enum payload calls;
- source-order field evaluation.

Copy aggregates execute through bytecode. Affine aggregate paths remain
explicitly rejected until O1.

## Phase O1 - Complete affine and strict-linear values

### Capability

- affine arguments, results, and temporaries;
- discarded affine expressions;
- transfers across blocks and cleanup scopes;
- loops and joins;
- nested projections;
- assignment replacement;
- path-dependent initialization and drop flags;
- deterministic reverse-initialization cleanup;
- strict-linear finite-exit checking.

### MIR responsibilities

- Represent every move and cleanup structurally.
- Reject unsupported user-visible partial moves.
- Preserve right-hand-side, destroy-old, initialize-new assignment order.
- Generate cleanup for return, break, continue, and discontinue edges.
- Verify strict-linear consumption on every finite exit.

### Talk IR responsibilities

- Lower explicit destroy and conditional destroy.
- Generate fieldwise destroy glue.
- Never infer cleanup from liveness or type shape at the target adapter.
- Verify glue identity, signature, and call sites.

### O1 exit fixtures

- `conditional_moves.tlk`;
- use after move;
- branch-specific and loop-carried move;
- early return cleanup;
- replacement assignment;
- nested affine aggregate cleanup;
- linear value consumed once;
- missing linear consumption rejected.

## Phase O2 - Borrows and complete provenance

O2 may develop in parallel with E1 and L1, but it cannot claim support until its
full source-to-LSP and source-to-backend handshakes land.

### Capability

- shared and mutable borrows;
- reborrows;
- field and payload projections;
- call argument-to-parameter transfer;
- borrowed method receivers;
- branch-specific endings;
- conflicts with move, write, destroy, and another borrow;
- v1 escape and suspension restrictions.

### Work

1. MIR emits structural borrow operations and canonical loan IDs.
2. Loan analysis computes conflicts and finite-path endings.
3. MIR verification checks every provenance chain.
4. Rejected diagnostics carry the same partial graph vocabulary.
5. Successful provenance queries traverse MIR operations.
6. The LSP source index remains disposable and calls the artifact query.
7. Talk IR erases source loans into explicit references or addresses only after
   verification.
8. The bytecode adapter executes shared reads and exclusive writes without
   learning source borrow semantics.

### O2 exit fixtures

- direct shared borrow;
- mutable borrow and writeback;
- projected reborrow;
- borrowed call argument;
- branch-specific loan endings;
- move while borrowed;
- competing mutable borrow;
- borrow escape;
- ordinary borrow across suspension rejected;
- successful and rejected LSP provenance rendering.

## Phase R1 - Managed storage, heap values, and generated glue

R1 had a mandatory design checkpoint because ADR 0032 did not completely define
executable heap-cycle and managed-storage semantics. P7 accepted Lane D's
[ADR 0033](adr/0033-managed-storage-heap-regions-and-ffi-lifetimes.md), with
Rust-shaped contract sketches in
[the R1 managed-storage contract sketch](r1-managed-storage-contract-sketch.md).
The semantic decisions are authoritative, but no production artifact or IR
shape exists until the coordinated G0 contract stack lands.

### Decisions closed by ADR 0033 before implementation

- executable meaning of `NominalRepresentation::Heap`;
- whether baseline cyclic object graphs remain required;
- region, tracing, type-specific reference-count, or other explicit cleanup
  mechanism;
- which operations are Talk IR operations and which are generated glue;
- resurrection and deinit ordering;
- CoW retain/release and element finalization.

ADR 0032's rejection of uniform reference counting remains in force. ADR 0033
selects merge-only heap regions and type-specific CoW for R1.

### Capability

- allocation and deallocation;
- heap-object fields;
- String and byte storage;
- Storage and Array;
- selected clone;
- Deinit;
- element destruction;
- CoW buffer sharing;
- Dict storage;
- direct heap-object cycles under the accepted merge-only region boundary.

### Guardrail

Do not map Talk IR onto the old runtime's object-region ledger merely because it
exists. Preserve accepted source semantics, but require the implementation to
fit behind the new Talk IR and backend interfaces.

### R1 exit fixtures

- `string_building.tlk`;
- `clone_method.tlk`;
- `heap_graph.tlk`;
- array clone then mutation;
- array growth with affine elements;
- array replacement destroys the old element;
- nested arrays;
- deinit ordering;
- balanced allocations for every executable fixture.

## Phase H1 - Closures, cells, and indirect calls

### Capability

- noncapturing function values;
- checked Copy, Move, shared-borrow, and mutable-borrow captures;
- closure environments;
- indirect calls;
- recursive and mutually recursive local functions;
- trailing blocks;
- compiler-managed cells for mutable Copy captures;
- closure cleanup.

### Ownership split

- TypedProgram selects capture modes.
- MIR verifies capture legality and escape.
- The lowerer performs closure conversion.
- Talk IR contains an explicit function and environment representation.
- The backend executes the closure calling convention without source capture
  rules.

### H1 exit fixtures

- anonymous application;
- returned closure;
- independent counters;
- closure argument;
- recursive local closure;
- mutation through a captured cell;
- escaping borrowed capture rejected;
- affine environment destroyed once;
- trailing block with early exit.

## Phase D1 - Existentials and dynamic dispatch

### Capability

- explicit and implicit existential packs;
- owned existential payloads;
- witness tables;
- dynamic requirement calls;
- associated-type bindings;
- existentials in records, enums, and arrays;
- GADT hidden payloads;
- payload cleanup through selected glue.

The current MIR likely needs an explicit existential representation. That must
be resolved through the contract-change protocol rather than encoded as an
unvalidated aggregate convention.

### D1 exit fixtures

- existential member dispatch;
- existential return and generic-bound dispatch;
- existentials in records, enums, and arrays;
- associated-type bindings;
- GADT hidden payload;
- existential deinit;
- borrow-to-owned pack rules.

## Phase C1 - Deep one-shot effects

C1 follows affine cleanup, strict linearity, managed environments, and closures.

### Capability

- dynamic nearest-handler routing;
- deep resumption;
- one-shot continuation consumption;
- Resume and Discontinue;
- implicit discontinue on finite handler return;
- cleanup across abandoned frames;
- checked handler captures;
- generic effect instantiations;
- effectful closures;
- strict-linear `ExactlyOnce` requirements.

### MIR work

- Verify published handler behavior against concrete CFG.
- Require one Resume or Discontinue on every finite clause exit.
- Attach discontinue cleanup to every suspension-capable call and perform.
- Reject ordinary loans across suspension.
- Verify balanced handler installation.
- Emit complete provenance for handler-captured shared loans.

### Talk IR and runtime work

- Lower direct Talk IR handler operations.
- Keep continuation representation private to each backend.
- Do not expose capability-passing CPS or restore lambda-G.
- Preserve cleanup order during nested aborts and finalizers.

### C1 exit corpus

- `handlers.tlk`;
- `caller_locals_handler.tlk`;
- `nested_handlers.tlk`;
- `resume_across_frames.tlk`;
- `multi_effect_handlers.tlk`;
- `generic_state.tlk`;
- `generic_two_instantiations.tlk`;
- `effectful_closures.tlk`;
- abort during cleanup;
- repeated perform through one deep handler.

The baseline handler-clause self-routing behavior is not required because ADR
0032 deliberately defines different dynamic routing.

## Phase K1 - Core library and host IO parity

### Capability

- Unicode strings and graphemes;
- iteration and `for`;
- arrays and dictionaries in ordinary programs;
- file IO;
- sockets, polling, and sleep;
- stdout and stderr;
- unsafe raw storage only through the approved seam;
- deterministic captured IO in tests.

Every core operation must be one of:

- a linked source-backed Talk IR supplier;
- an explicitly defined target-neutral intrinsic;
- a stable host import.

A backend-local name switch is not an acceptable semantic mapping.

### K1 exit fixtures

- `iterate_and_match.tlk`;
- `graphemes.tlk`;
- file write/read;
- socket loopback;
- split reads and writes;
- HTTP routing;
- negative IO counts;
- real socketpair integration where supported.

## Phase T1 - User-facing tool parity

Tools are restored only through the canonical pipeline.

### Incremental restoration

- After E1: `talk run` and Talk IR/bytecode inspection.
- After the source harness is stable: source `talk test`.
- After managed values and closures: executable REPL evaluation.
- After E2: package run and test.
- After bytecode serialization: emit-bytecode and run-bytecode.
- After runtime C-interface review: standalone executable builds.
- Restore `talk-c`, Swift, and wasm embedding through the same accepted runtime
  interface.

The old `lower` command's lambda-G output is not parity. If inspection commands
remain useful, expose canonical MIR, Talk IR, and target bytecode instead.

The baseline standalone path generated a C launcher around bytecode. Restoring
that path is tool parity; actual C translation is a separate target adapter.

## Phase B2 - Additional target adapters

After Talk IR supports calls, aggregates, cleanup, and managed storage, add
WebAssembly as the second independent adapter.

Recommended order:

1. bytecode reference backend;
2. WebAssembly;
3. C translation;
4. Cranelift;
5. LLVM.

A Talk IR row is multi-backend stable only after bytecode and Wasm execute the
same G5 fixtures. Cranelift and LLVM should not begin until two simpler adapters
have exposed target-specific assumptions in Talk IR.

## Dependency order and parallel work

The main dependency chain is:

```text
P0
 -> E1
 -> E2
 -> L1
 -> L2
 -> O1
 -> O2
 -> R1
 -> H1
 -> C1
 -> K1
 -> T1 completion
```

D1 can proceed after L1, L2, O1, and R1 and may run in parallel with H1. C1
waits for both H1 and the ownership/cleanup work. O2 provenance implementation
may begin in parallel with E1 but joins before borrow-capable source rows are
marked supported.

Within one vertical slice, work may be divided into:

| Lane | Scope |
| --- | --- |
| MIR | fixture, producer, diagnostics, verifier |
| Talk IR | fixture, lowerer, verifier |
| Backend | adapter/runtime support and G5 fixture |
| Observer | parity fixture, LSP/provenance, ledger |

Rules:

- no lane gets more than one slice ahead;
- fixture-only support remains rejected in production;
- contract changes serialize at G0;
- real handshakes serialize at G3;
- one integration owner rebases and runs G4/G5;
- complete vertical rows merge frequently;
- verifier strengthening invalidates stale downstream fixtures immediately;
- branch-local green tests never advance the ledger.

## Black-box oracle and hardening

### Before a second backend

Freeze reviewed expected results, output, diagnostics, and resource behavior from
the baseline. Do not add a replacement evaluator.

### After Wasm connects

Run every shared G5 fixture through bytecode and Wasm. Expected outputs remain
authoritative; backend agreement is an additional differential oracle.

### Resource correctness

The reference runtime tracks live allocations, objects, regions, and external
resources as applicable. Every successful black-box test asserts balance unless
the returned value intentionally owns the resource and the harness accounts for
that result footprint.

Double free, use after free, invalid bytecode references, and corrupt serialized
images fail deterministically rather than panic or execute unchecked.

### Generated and fuzz coverage

After E1, add deterministic generated CFG cases for verifier and backend
agreement. After O1/R1, add ownership combinations that vary branches, loops,
temporaries, aggregates, and cleanup. Any quarantined generated case becomes a
named expected-failure row in the parity ledger; there is no anonymous skip
list.

## Full parity exit criteria

Feature and tool parity is reached when:

- every **Required parity** row passes G0-G5 on bytecode;
- all 16 archived corpus programs have reviewed expected output and balanced
  resources;
- archived acceptance and rejection behavior has been replayed, with every
  difference dispositioned;
- no parity-required feature reaches an unsupported MIR or Talk IR path;
- ownership and borrow failures have source-backed diagnostics;
- successful and rejected borrow provenance is available through the LSP;
- module supply and signatures verify through execution;
- run, source tests, package execution, REPL evaluation, bytecode emission,
  standalone builds, and embeddings use the canonical pipeline;
- no backend reads TypedProgram or CheckedMir;
- no old evaluator or lambda-G semantic authority has returned;
- the status and parity ledgers contain no unclassified required gaps.

Backend breadth then proceeds row by row. It does not reopen source semantics.

## Parallel implementation plan after E2 scalar globals

The next work is split into three implementation lanes and one design lane.
Parallel work is permitted only while the artifact interfaces and file ownership
below remain fixed. A lane may add temporary construction maps inside its owning
phase, but may not publish a second semantic artifact or add an older artifact
as an input.

All lanes start from `bigdiff` after this planning update is merged, with
`bd5ac7c0` (`e2: initialize linked scalar globals`) as the required implementation
ancestor, in separate worktrees. Each lane keeps commits reviewable and
independently green. Do not include the unrelated `core/Array.tlk` worktree
change in any backend commit.

Suggested setup after the planning commit is on `bigdiff`:

```sh
git worktree add ../talk-lane-a -b lane/e2-package-graph bigdiff
git worktree add ../talk-lane-b -b lane/l1-specialization bigdiff
git worktree add ../talk-lane-c -b lane/borrow-provenance bigdiff
git worktree add ../talk-lane-d -b lane/r1-storage-design bigdiff
```

One person or agent owns each lane branch. Do not share an uncommitted worktree.
A lane rebases on `bigdiff` only at a named integration checkpoint, reruns its
full affected suite, and reports the exact commit and validation results before
merge.

### Frozen interfaces during parallel work

Until the first integration checkpoint, these interfaces are fixed:

- MIR consumes only `ValidatedTypedProgram` and publishes only `CheckedMir`;
- Talk IR lowering consumes only `CheckedMir` and publishes only a verified
  `TalkIrModule`;
- package orchestration supplies the existing Talk IR linker with verified
  `(StableModuleId, TalkIrModule)` inputs and one root ID;
- external call supply remains exact `(StableModuleId, export, signature)`
  matching with exactly one supplier;
- selected witness and implementation IDs come from TypedProgram/MIR facts;
  specialization may substitute them but may not perform conformance search;
- target execution accepts only `ValidatedBytecodeModule`;
- unsupported forms reject before partial lowering, linking, or execution.

A required interface change stops the affected lanes. Record the change in ADR
0032 and Stage 0, merge it as a small contract checkpoint, then rebase all lane
worktrees before continuing.

### Lane A - package graph production

**Goal:** compile and execute a real package graph using the already verified
scalar module/linker/runtime path.

**Primary ownership:**

- `src/compiling/package.rs` and additive package-build modules;
- additive driver orchestration APIs in `src/compiling/driver.rs`;
- package integration tests and, only after the API passes, package-aware CLI
  dispatch in `src/bin/talk.rs`.

**Files this lane must not redesign:**

- `src/talk_ir/linking.rs`;
- MIR or Talk IR contract types;
- scalar bytecode semantics.

**Implementation steps:**

1. Define an ephemeral package build plan containing module source locations,
   dependency edges, root target, and deterministic module order. It is build
   orchestration, not a semantic IR, and must not duplicate types, witnesses,
   exports, or initialization facts.
2. Resolve the selected library or binary target from `package.tlk` and the
   existing lock/install state. Reject missing targets, duplicate module names,
   unresolved dependencies, and package dependency cycles before compilation.
3. Compile each source module through the ordinary frontend. Export its
   `ModuleInterface`, assign its `StableModuleId`, and install that interface in
   the dependent module's `ModuleEnvironment`. Do not synthesize link names in
   package code.
4. For every error-free module, run the canonical pipeline:
   `TypedProgram -> CheckedMir -> TalkIrModule`. Retain only the verified Talk IR
   module and stable ID for linking.
5. Invoke the existing Talk IR linker once with the complete verified module
   set and the selected root ID. Do not add linker fallback, partial linking, or
   package-specific import matching.
6. Select the root entry using the existing scalar entry rules, compile the
   linked Talk IR to `ValidatedBytecodeModule`, and execute through
   `ScalarExecutable` so Talk rendering and zero-resource checks remain shared.
7. Add package-level `run` wiring only after the orchestration API has direct
   tests. Explicit filename execution must keep its current behavior.

**Required tests:**

- one package binary calling a dependency function;
- a dependency function whose module owns a private helper;
- dependency and root dynamic globals proving supplier-before-consumer,
  source-order, and once-only initialization;
- missing, duplicate, incompatible, and cyclic package/module supply;
- ambiguous or missing package entry;
- zero allocation/object balance for successful scalar package execution;
- a fail-closed package using an unsupported generic, aggregate, or external
  global form.

**Lane A exit:** a package graph reaches validated bytecode without changing
linker semantics. Package `run` is not marked integrated until its black-box
fixture passes G0-G5.

### Lane B - L1 specialization and selected implementation materialization

**Goal:** turn generic scalar MIR calls and frontend-selected implementation
calls into monomorphic Talk IR without downstream semantic search.

**Primary ownership:**

- generic-call preservation in `src/mir/generate.rs` and generic contract/call
  verification in `src/mir/verify.rs`;
- a new specialization implementation owned by MIR-to-Talk-IR lowering;
- narrowly scoped changes in `src/talk_ir/lowering.rs`;
- L1 source, fixture, verifier, and execution tests.

**Implementation steps:**

1. Stop rejecting a validated generic direct call solely because its canonical
   instantiation is non-empty. Preserve the exact callable `ItemId`, ordered type
   arguments, and selected witness arguments in CheckedMir. MIR verification
   checks arity, substitution completeness, concrete arguments for the L1
   scalar subset, and agreement with the callable contract.
2. Introduce a temporary specialization key inside Talk IR lowering. The key is
   the canonical callable item plus its fully ordered concrete type arguments
   and already-selected witness arguments. It is a worklist key, not a new
   artifact or persistent side table.
3. Seed the worklist from entrypoints, exports, global initializer functions,
   and direct calls. Allocate each key once before lowering bodies so recursive
   specializations resolve to their preallocated `IrFunctionId`.
4. Substitute callable contracts, locals, constants, direct callees, return
   types, and scalar intrinsic signatures from the key. Reject any residual type,
   effect, row, permission, or witness parameter before publishing Talk IR.
5. For `Callee::Witness`, use the exact frontend-selected implementation ID.
   Specialize that implementation under the published arguments. Never search
   conformances, requirements, module interfaces, or display names downstream.
6. Keep external specialization fail-closed in Lane B. Record the exact demanded
   callable, concrete arguments, selected witnesses, and resulting monomorphic
   signature in a negative fixture, but do not invent a supplier export or pass
   a demand side table across the CheckedMir-to-Talk-IR seam. Cross-module
   specialization supply requires the later contract checkpoint below.
7. Re-verify the complete Talk IR candidate and keep unsupported storage,
   effects, aggregates, closures, and external generic supply fail-closed.

**Required tests:**

- one generic scalar identity call;
- two concrete instantiations of one generic body;
- recursive specialization with preallocated identity;
- duplicate call sites deduplicating to one specialization;
- selected normal `+` and comparison reaching an exact local implementation or
  audited imported scalar recipe, plus explicit rejection of an unselected
  protocol default;
- malformed argument arity, residual generic type, mismatched selected
  implementation, and external generic supply rejection;
- no-conformance-search law test;
- source-to-bytecode execution for each admitted local generic scalar call.

**Lane B exit:** local generic scalar calls and locally supplied selected
implementations execute through verified Talk IR and validated bytecode. Lane B
kept external generics fail-closed; the later P4 simplification admitted only
exact exported scalar recipes and left general external generic bodies blocked.

### Lane C - borrow provenance correctness

**Goal:** produce complete structural borrow provenance and expose it to valid
LSP queries and rejected-program diagnostics without changing execution
semantics.

Lane C has two provenance stages, named Prov-1 and Prov-2 to avoid collision
with the plan's C1 effects phase and the historical reset contract labels.

**Stage Prov-1 primary ownership:**

- a dedicated MIR provenance/query module using the existing contract shapes;
- fixture constructors and verifier/query tests kept inside that module (apart
  from the one module declaration, Prov-1 does not edit `src/mir/generate.rs`,
  `src/mir/verify.rs`, or the core MIR contract definitions);
- analysis and LSP result rendering that consumes verified fixture events.

**Stage Prov-1 instructions:**

1. Use the existing contracted `BorrowSubject`, `BorrowEvent`, edge, query, and
   diagnostic shapes from ADR 0032 and Stage 0. Do not introduce parallel event
   identities or a second provenance result type.
2. Build provenance from structural owner, borrow, reborrow, projection,
   transfer, use, conflict, and end events. Do not infer provenance from
   liveness, source ASTs, or diagnostic text.
3. Verify event endpoints, function/subject identity, parent edges, place/type
   agreement, and source origins. Invalid event graphs cannot publish query
   results.
4. Implement deterministic owner-to-use and conflict-subgraph queries over a
   verified fixture graph.
5. Add LSP rendering tests against those query results, but do not claim source
   production support yet.

**Stage Prov-2 after Lane B releases `src/mir/generate.rs`:**

1. Construct structural MIR places, loans, transfers, and endings, then derive
   the same events without adding a persistent provenance side table.
2. Attach complete provenance subgraphs to borrow diagnostics before publishing
   no `CheckedMir` for rejected programs.
3. Connect successful source queries and rejected-program diagnostics to the
   LSP; retained ASTs provide ranges only.

**Required tests:** direct borrow, reborrow, field projection, mutable conflict,
call argument transfer, closure and handler capture fixtures, branch-specific
ends, and rejected-program provenance completeness.

**Lane C exit:** both successful and rejected source programs have complete,
source-backed provenance. Fixture-only rendering is an intermediate checkpoint,
not integration.

### Lane D - R1 managed-storage design checkpoint

**Goal:** settle representation and lifetime contracts before implementation.
This lane is design-only while A-C execute.

**Primary ownership:** ADR 0008, ADR 0012,
[accepted ADR 0033](adr/0033-managed-storage-heap-regions-and-ffi-lifetimes.md),
and [R1 contract sketches](r1-managed-storage-contract-sketch.md) only. It
must not modify runtime, MIR, Talk IR, or backends before review.

**Questions that must be closed:**

- owned buffer and borrowed grapheme representations;
- how concrete Byte values are produced from managed storage;
- aggregate field ownership and projection addresses;
- clone, destroy, deinit, and copy-on-write ordering;
- cyclic heap policy and whether cycle collection is in v1;
- FFI pinning, host handles, and external resource balance;
- target-neutral Talk IR operations versus backend-specific layout.

**Lane D exit:** an accepted ADR with cross-artifact laws, verifier obligations,
resource oracles, and explicit deferred cases. Acceptance permits the
coordinated G0 contract stack; managed-storage implementation remains blocked
until that stack lands.

### Work that remains sequential

- Exact external scalar globals remain a dedicated E2 cross-cut after Lane A.
  Before adding global imports to every artifact and the linker, audit whether
  exact generated getter/setter callables preserve identity, mutability, and
  initialization ordering with the existing callable contract. Any accepted
  form must not run concurrently with edits to the same seams.
- General cross-module generic bodies remain fail-closed. Audited imported
  scalar implementations no longer need specialization supply. A future generic
  module-ABI checkpoint must still explain exact demand/supply without a
  persistent semantic side table, generic Talk IR, or downstream conformance
  search.
- Package-level local generic execution is integrated. Package-level calls to
  arbitrary external generic bodies wait for that future module-ABI checkpoint.
- Prov-2 starts only after Lane B releases MIR generation ownership.
- The managed-storage G0 stack starts only after Lane D's ADR is accepted;
  implementation starts only after G0 lands.
- Wasm/C widening may proceed independently only against an already integrated
  verified Talk IR subset; it may not drive source or IR contract changes.

### Integration checkpoints and merge order

1. **P1 - independent lane review:** complete; A, B, and Prov-1 passed their
   targeted suites, formatting, diagnostics, and diff checks in their own
   worktrees. D produced the design later accepted at P7.
2. **P2 - primary checkout validation:** complete; Lane A and Lane B were merged
   independently and the complete workspace suite passed. Their ledger conflict
   was resolved by preserving both exact package-supply and specialization
   identities.
3. **P3 - A/B coexistence handshake:** complete; a real package root uses a
   locally defined generic scalar specialization from a root global initializer
   and calls a monomorphic dependency with dependency globals. Package
   orchestration, local specialization, linking, initialization, G0-G5, and zero
   resource balance pass without claiming external generic supply.
4. **P4 - imported scalar implementation simplification:** complete for
   exported callables whose complete validated body is one scalar intrinsic.
   Canonical interfaces publish the exact recipe, MIR materializes it after
   frontend witness selection, and normal Core scalar operators execute without
   specialization or linker changes. Arbitrary cross-module generic bodies stay
   fail-closed and require a separate module-ABI checkpoint when a real parity
   slice needs them.
5. **P5 - provenance production:** in progress; fixture infrastructure and the
   first production shared Copy-scalar slice are integrated. Structural loans,
   call transfers, uses, finite-path endings, successful artifact queries, and
   source-position LSP rendering are connected. Mutable, projected, reborrowed,
   captured, suspension-sensitive, and rejected-program cases remain.
6. **P6 - external scalar globals:** complete for source-backed reads of
   immutable monomorphic Unit, Bool, Int, and Float globals. Exact generated
   zero-parameter readers preserve global/module/type/mutability identity and
   use existing callable supply, initialization ordering, linking, and negative
   checks. Mutable globals, writes, aggregates, managed storage, and
   precompiled-only readers remain fail-closed.
7. **P7 - storage decision:** complete; ADR 0033 is accepted. R1 code remains
   blocked until the coordinated G0 contract stack lands.

At every checkpoint run `cargo test --workspace --exclude www`,
`cargo check --workspace --exclude www`, `cargo fmt --all -- --check`, structured
workspace diagnostics, `git diff --check`, and the `talk-syntax`/`talispk`
frontend smoke checks. Update ADR 0032, Stage 0, backend status, and the parity
ledger in the same commit that advances a capability row.

## Simplification audit for remaining checkpoints

- General cross-module generic-body supply is deferred. Do not introduce a
  package-wide specialization coordinator merely to unlock a closed intrinsic
  or generated-callable case.
- P6 proved generated scalar readers sufficient without external-global
  variants in MIR, Talk IR, or the linker. Later mutable/write support must not
  infer setter semantics from this read-only contract.
- Prov-2 derives successful provenance from structural CheckedMir operations and
  uses function-scoped temporary generation state for rejected programs; it
  does not add a persistent provenance graph.
- L2 should land the smallest closed aggregate representation first and keep
  pattern compilation and backend layout as separate reviewed slices.
- O1 continues to lower explicit MIR moves, destroys, and drop flags rather than
  introducing target ownership inference.
- R1 implementation should stage managed buffers before heap regions and host
  resources while preserving ADR 0033's distinct accepted policies and shared
  G0 vocabulary.

## Immediate next actions

1. Continue production borrow provenance from the integrated shared
   Copy-scalar call slice into mutable writeback, projections, reborrows,
   captures, conflicts, escapes, suspension checks, and rejected-program LSP
   diagnostics.
2. Begin the smallest closed Copy-aggregate representation only as a separate
   reviewed slice; keep pattern compilation and backend layout separate.
3. Keep managed-storage implementation blocked until the coordinated G0
   contract stack and ownership/aggregate/borrow prerequisites land. Preserve
   fail-closed unsupported forms and the scalar resource baseline.
