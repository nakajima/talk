# 0040 - Frame-or-region closure environments without an escape pass

Status: folded into ADR 0044 (proposed)

## Context

Talk closures currently carry a target chunk and an `Rc<Vec<Value>>`
environment in the bytecode interpreter. The Rust `Rc` keeps the vector's bits
alive, but it is not a Talk ownership mechanism: cloning or dropping it does
not retain or destroy managed buffers, region claims, generic values, cells, or
other closure environments.

MIR works around that limitation by keeping ownership-sensitive captures in
the creating frame. An implicit owned capture receives a retained snapshot in
a frame-owned local; a consuming capture moves into a frame-owned slot; a
shared borrowed capture continues to refer to frame-owned state. The closure's
environment contains only a shallow copy of the runtime value. The
`anchored_closures` tracker then rejects any return or store that might outlive
the frame:

```text
a closure that captures owned values cannot escape its creating scope
(not supported yet)
```

This is correct as a temporary safety fence but rejects valid programs such as
a function returning a closure over a `String`. ADR 0037 requires owning
closure environments so those programs execute and balance. ADR 0038 requires
capture legality and operations to come from checked capture facts while MIR
owns environment layout and runtime lifetime.

Putting every closure environment in a managed heap region would remove the
fence, but it would also allocate for common synchronous trailing blocks and
local helper closures that cannot escape. Captureless function values need no
environment at all. A separate post-MIR escape-analysis pass could recover
those cases, but it would add another compiler stage and another whole-body
traversal to the lean backend prohibited by ADR 0034's depth and staging
criteria.

The existing MIR builder already observes the relevant flow while emitting
instructions. It propagates anchored closure marks through copies and block
parameters and recognizes the edges it currently rejects. The missing design
is not another analysis pass; it is a representation plan that this existing
online tracking can update instead of reporting a capability error.

## Decision

Closure environments have three storage classes:

```text
EnvironmentStorage
  Empty   - the closure captures no runtime values
  Frame   - the environment is owned by the creating activation
  Region  - the environment is an owning member of a managed region
```

A closure value remains a small pair of code identity and an environment
reference. The environment, not the code value, receives the selected storage.

- Captureless closures use `Empty` and allocate nothing.
- A capturing closure starts with a `Frame` plan.
- If MIR construction observes that the closure may outlive the creating
  activation, it changes that plan to `Region`.
- If a closure with a non-promotable borrowed capture may escape, MIR reports a
  structured borrow-escape diagnostic rather than a backend capability error.
- Uncertain ownership-transfer edges select `Region`. Optimization may be
  conservative; lifetime safety may not be.

There is no post-MIR escape pass and no runtime promotion from frame to region
storage.

## Online environment planning

Each closure construction receives an `EnvironmentId`. The function builder
holds one mutable plan per environment:

```text
EnvironmentPlan
  storage: Empty | Frame | Region
  slots: ordered checked capture and inherited-environment slots
  borrowed: source origins of non-owning slots
```

MIR values carry environment provenance during the same construction walk that
currently carries `anchored_closures`. Provenance is a set of
`EnvironmentId`s because aggregates and outer closures may contain several
closure values.

The builder applies these rules while emitting existing MIR:

- `MakeClosure` defines its own environment provenance and inherits the
  provenance of closure values captured in its slots.
- `Copy` propagates provenance to its destination.
- tuples, records, variants, existential packages, and other value aggregates
  union operand provenance into their destination instead of treating
  aggregate construction itself as an escape.
- `SetField` on a local value propagates source provenance into the updated
  local.
- `Goto` propagates argument provenance to block parameters exactly as the
  current anchored tracker does.
- branch joins union provenance conservatively.

An owning lifetime sink marks every environment in the operand's provenance as
`Region`:

- return from the creating activation;
- global storage;
- object or raw managed storage;
- finalizer storage;
- an owning or consuming call argument whose contract permits retention;
- abort delivery across the creating activation;
- any boundary whose checked ownership contract is unavailable.

A checked borrowed/noescape argument is not an escape sink. Calls use the
checked argument operations published through `TypedProgram`; MIR does not
reconstruct the decision from source markers or runtime representation.

Cell storage is conservatively an escape sink in the first implementation.
The classification may later keep a cell frame-local only when the existing
online provenance proves that both the cell and every closure sharing it remain
in the activation. That refinement does not change this ADR's representation.

The plan is mutable until the function builder finishes. `MakeClosure` and
environment ownership operations refer to `EnvironmentId`, so lowering reads
the final plan directly. This is ordinary backpatching inside the existing MIR
builder, analogous to reserving function and block identities before their
contents are complete. It is not a second traversal.

## Environment ownership

Every environment slot is described by the checked operation published for
that capture or inherited value:

- a Copy capture stores the copied scalar or aggregate;
- a snapshot capture retains once at environment construction;
- a consuming capture transfers ownership into the environment;
- an owning stored view retains its referent according to the checked
  promotion operation;
- a shared or exclusive borrowed capture owns nothing and records its source
  lifetime;
- inherited generic evidence uses its published ownership contract;
- a cell slot carries the cell's managed environment handle.

Both frame and region environments own the slots described as owning. The
storage class changes where their generated teardown runs, not the checked
capture operation.

### Frame environments

A frame environment is stored in the creating runtime activation and is
addressed by a stable frame identity plus an environment slot. It must not be a
pointer into a movable Rust `Vec<Frame>` or into a register allocation.

The compiler includes frame-environment teardown in the creating function's
existing structural cleanup on normal return, early return, loop exit, handler
resume, and discontinue unwind. The environment releases each owning slot
exactly once in reverse slot order. Calling the closure borrows the environment
for the call and performs no retain or release.

A runtime identity check traps if malformed bytecode attempts to call a frame
environment after its activation has ended. Valid bytecode cannot trigger that
trap because the MIR plan admits `Frame` only when no owning escape edge was
observed.

### Region environments

A region environment is an internal managed-region member. The region's
external root is the closure value. Copying an owned closure reference acquires
a region claim; destroying it releases the claim. The last external claim runs
the compiler-generated environment teardown and then frees the environment.

The existing region arena is generalized from source `'heap` records to typed
managed members:

```text
ManagedMember
  SourceObject
  ClosureEnvironment
  Cell
```

All member kinds share region identity, external-root counting, merge-only
internal edges, deterministic finalization, resurrection checks, and bulk
freeing. Source object counts remain distinguishable from internal closure and
cell counts in balance reports.

Storing a region-bearing capture into an environment merges its region with the
environment's region and converts the stored edge to an internal edge. This
extends ADR 0033's existing object-cycle rule to closure and cell members
without introducing tracing collection or a second reference-counting system.
The generated environment teardown destroys buffer-owning and generic slots;
region-internal member edges are finalized by the merged region rather than
released as external roots.

Environment teardown is generated MIR, not a runtime type table. Generic slots
use the drop witnesses stored in the same environment. The runtime schedules
the generated finalizer through the existing deterministic region-finalization
mechanism; it does not interpret Talk types or choose destruction operations.

## Closure and cell representation

The runtime closure representation becomes conceptually:

```text
ClosureValue
  chunk: ChunkId
  environment: Empty | Frame(FrameIdentity, EnvironmentSlot)
                     | Region(ManagedMemberId)
```

`EnvGet` reads through that environment reference. Direct calls continue to use
`Empty`.

Assignment-converted cells use the same managed-member substrate. A frame-only
cell may remain activation-owned. A cell reachable from a `Region` environment
is a region member; storing a closure back into that cell merges the two
regions. Recursive and mutually recursive local closures therefore do not form
a separate Rust-`Rc` cycle and do not depend on the process-lifetime slot arena.
The cell's generated teardown destroys its current owning value exactly once.

## Borrowed captures

Heap allocation does not make an arbitrary borrowed capture safe.

When online planning changes an environment to `Region`, every borrowed slot
must have one of these checked dispositions:

1. its lifetime is proven to include the escape extent under a named language
   rule;
2. typing selected an owning stored-view promotion, and environment
   construction performs that promotion; or
3. the program is rejected with a structured borrow-escape diagnostic carrying
   the capture and sink origins.

MIR does not silently retain an exclusive borrow, convert aliasing semantics,
or reinterpret a capture mode to make promotion possible. Owned snapshots and
consuming captures are the valid behavior that removes the current
`anchored_escape` capability rejection. Genuine invalid borrowed escapes remain
ownership errors.

## Nested closures and aggregates

Environment provenance is transitive. If an outer closure captures an inner
closure and the outer closure escapes, both environments become region-backed.
The same applies when closures are nested in tuples, records, variants, or
existentials before reaching a sink.

Constructing an aggregate is not itself proof of escape. A tuple of closures
used entirely within one activation may retain frame environments. This is why
the current `track_anchored` behavior of rejecting at aggregate construction is
replaced by provenance propagation.

In-place mutation that the online tracker cannot summarize safely is
conservative: affected environments become `Region`. More precise tracking may
be added inside the builder only when it removes a measured allocation and does
not add another body pass.

## Bytecode and validation

Bytecode distinguishes empty, frame, and region environment construction. The
serialized form contains the selected storage class, environment layout width,
and generated teardown chunk where required. It does not contain source capture
modes or types.

Bytecode validation checks:

- referenced chunks and environment slots exist;
- frame-environment operations occur only in chunks that declare the matching
  layout;
- region environments name a valid generated teardown chunk;
- environment accesses stay within the declared width; and
- malformed storage tags or handles are rejected before execution.

Validation does not repeat escape analysis. The allocation class is trusted
compiler output when produced in-process and validated structure when loaded
from bytes.

## Implementation order

1. Replace the boolean `anchored_closures` set with online
   `EnvironmentId` provenance and mutable plans, initially preserving the
   current rejection behavior.
2. Propagate provenance through copies, block parameters, and value aggregates;
   classify existing rejection edges as owning sinks or borrowed-escape errors.
3. Add `Empty` and stable frame-environment runtime representations; remove the
   `Rc<Vec<Value>>` environment from nonescaping closures.
4. Generate one environment teardown description from checked slot facts and
   run it from existing frame cleanup.
5. Generalize the managed-region arena with closure-environment members and
   lower `Region` plans through it.
6. Make function values participate in retain, destroy, aggregate ownership,
   and generic ownership witnesses.
7. Move assignment-converted escaping cells onto managed members and close
   recursive closure/cell cycles.
8. Remove `anchored_escape()` and the corresponding
   `BackendError::unsupported` sites. Preserve genuine borrowed-escape failures
   as structured MIR diagnostics.

Each step keeps the public `compile` and `execute` seams unchanged and lands
with black-box execution and balance coverage.

## Validation

Required tests include:

- captureless function values allocate no environment;
- an immediately called capturing trailing block uses a frame environment;
- a closure passed through a checked borrowed argument remains frame-backed;
- returning a closure over a managed `String` selects a region environment,
  executes after the creator returns, and frees exactly once;
- storing a closure in a global, object, existential, and returned aggregate
  selects a region environment;
- a local aggregate containing closures does not force region allocation until
  the aggregate reaches an owning sink;
- copies, branches, and block-parameter joins preserve environment provenance;
- an escaping outer closure promotes environments of captured inner closures;
- consuming and snapshot captures balance on normal return, early return,
  resume, and discontinue;
- generic owning captures invoke the stored drop witness exactly once;
- an escaping borrowed capture reports the capture and escape sink without
  reaching backend capability rejection;
- independent recursive closure/cell groups tear down without leaks;
- closure/cell cycles merged with source heap objects finalize and free as one
  region;
- runtime identity checks reject a malformed call through a dead frame
  environment;
- bytecode encode, decode, and validation preserve the selected storage class;
  and
- balance reporting distinguishes source heap objects, closure environments,
  and cells.

Tests assert allocation class through counted runtime instrumentation, not by
matching disassembly or relying on optimizer behavior.

## Alternatives rejected

### Put every capturing closure environment in a region

This is the simplest lifetime rule, but it allocates and updates region claims
for synchronous trailing blocks and local closures that provably die with their
activation. The existing builder already observes enough flow to avoid that
cost without another traversal.

### Add a post-MIR escape-analysis pass

Rejected. It adds another whole-body stage, duplicates flow already observed by
MIR construction, and conflicts with ADR 0034's requirement that private stages
justify their existence through a distinct responsibility. Online planning can
make the same conservative decision while the builder emits the relevant edge.

### Publish a frontend `escapes` bit

Rejected. Escape-based storage selection is runtime representation and CFG
flow, both owned by MIR under ADR 0038. Making typing's answer load-bearing for
allocation would recreate a second code-generation authority and would require
the frontend to understand backend storage boundaries.

### Dynamically promote a frame environment at an escape instruction

Rejected. Existing aliases would need forwarding or rewriting, consuming and
linear captures would need transactional ownership transfer, and promotion
across branches and unwind edges would introduce runtime state and failure
modes. Static online backpatching chooses one representation per closure site
before bytecode emission.

### Use Rust `Rc` destruction for owning environments

Rejected. Interpreter register copies change Rust strong counts without Talk
ownership operations, and Rust `Drop` cannot execute the required generated MIR
with generic witnesses and deterministic effect-unwind ordering. `Rc` cycles
through cells would also leak independently of Talk's region cycle design.

### Introduce a separate closure reference-counted heap

Rejected. It duplicates external-root accounting, finalization, resurrection,
cycle handling, diagnostics, and balance instrumentation already provided by
managed regions. Closure and cell edges must compose with source heap objects,
not form an independently managed graph.

## Relationship to earlier decisions

This ADR implements the owning-closure-environment requirement in ADR 0037 and
preserves ADR 0038's division of responsibility: typing publishes checked
captures; MIR chooses layout and lifetime; the runtime executes explicit
operations.

It preserves ADR 0034's one deep backend interface and explicitly declines to
add another backend pass.

It extends ADR 0033's managed-region substrate to closure environments and
cells. It supersedes ADR 0033's v1 rejection of escaping closure environments
and deferral of closure/cell cycles only for combinations admitted by the
checked-capture and region-member rules above. ADR 0033's restrictions on raw
storage, FFI escape, resurrection, and independently managed buffer graphs
remain in force.

It does not revive ADR 0029's rejected uniform-reference-counting baseline.
Only environments that may outlive an activation become region roots;
frame-local environments and captureless closures do not acquire universal
reference counts.

## Consequences

- Valid owned captures can escape without dangling frame state.
- Captureless and proven nonescaping closures avoid managed-region allocation.
- The existing builder's safety tracker becomes a representation planner rather
  than a capability-rejection mechanism.
- No new compiler pass or frontend escape authority is introduced.
- Conservative uncertainty costs a region allocation, not correctness.
- Function values become real owning runtime values when region-backed.
- Closure, cell, and source heap cycles share one deterministic region
  lifecycle.
- The runtime and bytecode gain two environment representations and explicit
  internal managed-member kinds.
- Environment provenance increases local MIR-builder bookkeeping; this is the
  accepted cost of avoiding both universal heap allocation and a separate
  analysis pass.
