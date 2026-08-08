# 0044 - The unified memory model

Status: proposed; on acceptance supersedes ADR 0033 (managed storage, heap
regions, and FFI lifetimes) and ADR 0040 (frame-or-region closure environments)

## Context

ADR 0033 defined the managed-storage contract: reference-counted buffers,
merge-only heap regions, and affine host handles. ADR 0040 designed owning
closure environments on top of it. Read together they describe one model in
two documents, and 0033's boundary rejected exactly the closure and cell forms
that 0040 then admitted, so the pair only made sense as a sequence. This ADR
states the single end-state model. There is no interim closure restriction in
the design; the current implementation fence (`anchored_closures`) is a
work-program matter tracked by ADR 0037, not a phase of the model.

Authority boundaries come from ADR 0038 and staging constraints from ADR 0034.
This ADR changes neither. ADR 0029 (uniform reference counting) remains
rejected.

## The model

Four rules. Everything after this section is a consequence of them.

### 1. Authority flows one way

Typing publishes checked facts: capture operations, Alias/Move/Borrow edges,
clone and `Deinit` witnesses, evidence and effect contracts. MIR chooses
representation, layout, and lifetime. The runtime executes explicit
operations; it does not inspect Talk types, scan source, or infer ownership
from liveness or display names. No layer reconstructs another layer's
decision.

### 2. Four substrates, one lifecycle rule each

Every runtime value is owned by exactly one substrate:

- **Frame** - the creating activation. Teardown runs in reverse slot order on
  every exit edge: normal return, early return, loop exit, handler resume,
  and discontinue unwind. No counts of any kind.
- **Buffer** - one type-specific reference-counted control block with a
  contiguous element payload. Copy-on-write sharing; the final owner destroys
  every initialized element and deallocates.
- **Region** - a merge-only set of managed members with a count of external
  roots. Member kinds: heap objects, closure environments, and cells.
  Internal edges (object fields, captured members, cell contents) add no
  external root. When the count reaches zero the region finalizes
  deterministically and frees as a unit. Cycles internal to a region do not
  keep it alive.
- **Host** - an opaque affine handle with an explicit close contract. No
  count, no implicit clone.

These substrates do not share one universal retain/release rule.

### 3. Selection is online, per-site, and monotone

Where a value can live is decided by MIR while it builds the function, at each
construction site, from flow that construction already observes. A site starts
at the cheapest substrate (frame) and latches toward the conservative one
(region) when an owning sink is observed. The latch never moves back. There is
no separate analysis pass (ADR 0034), no frontend escape bit (ADR 0038), and
no runtime promotion between substrates.

Function boundaries are themselves sinks, so selection is per-function and
needs no interprocedural summaries. A call with a checked borrowed or noescape
argument is not a sink; an owning or consuming argument whose contract permits
retention is. Uncertainty costs a region allocation, never correctness.

In this version of the model, closure environments and cells are the only
value kinds with a real substrate choice. Heap objects are always region
members because they have identity; buffers and host handles are fixed by
type and import contract.

### 4. Soundness comes from checked facts; substrate choice is optimization

Legality - a borrow never escapes, a linear value is consumed once, an alias
acquires exactly one root - is enforced entirely by rule 1's checked facts and
holds under any substrate choice. Choosing frame over region changes where
teardown runs, never what it does. A design that needs a frontend escape
decision to be *correct* violates this rule.

## Ownership edges

Type checking selects Alias, Move, or Borrow contextually and never from
last-use liveness:

- a borrow parameter, borrowed receiver, or explicit borrow context selects
  `BorrowShared` or `BorrowMut` and adds no root;
- an explicit `consume`, a parameter whose selected passing mode is Consume,
  an owned return edge, or another explicit ownership-transfer context selects
  Move and makes the source unavailable on that path;
- an ordinary owning place use of a heap reference selects Alias, including a
  local binding, assignment RHS, value-aggregate field, or heap-field
  initialization that does not explicitly consume its source;
- a fresh heap rvalue already owns one root and moves that root into its
  owning destination rather than aliasing itself;
- the same rules apply recursively to a value aggregate containing heap
  references: an ordinary duplicate requires structural Alias evidence, while
  a consuming argument, owned return, or explicit transfer moves the
  aggregate.

`NominalRepresentation::Heap` means identity and shared reference semantics.
Heap types cannot declare `Copy` or `CheapClone`; intrinsic reference aliasing
is not a value-copy conformance and adds no `.clone()` witness. Every source
heap duplication carries a distinct checked Alias edge with structural alias
evidence; lowering turns it into exactly one external-root acquisition per
represented heap reference. Constructor and assignment production preserve the
selected edge for each source operand. A backend may not turn a last use into
Move or omit an Alias acquire.

Structural Alias is limited to lifecycle-trivial value products. Anonymous
tuples and closed records qualify when every component has exact Copy or Alias
evidence. A nominal value struct additionally qualifies only when it has no
user `Deinit` hook, no custom clone/destroy lifecycle, no hidden storage, and
its complete canonical field list is proven component-by-component. A nominal
with its own hook requires an independently selected Copy or clone authority,
or the value must Move. This prevents one unapproved source use from creating
two nominal instances and two hook invocations.

Move between already-external storage transfers an existing root and produces
no acquire. Moving out of region-internal storage is not an ordinary Move: it
must externalize first, as defined under regions below.

## Aggregate fields and internal addresses

A value aggregate owns every initialized owned field. A move transfers that
ownership; an Alias, Copy, or selected clone operation is explicit. A backend
may not infer field retains from a bit copy.

Internal addresses are scoped capabilities, not source values. Talk IR may
form addresses for stack slots, globals, value-aggregate fields, and buffer
slots, but an address:

- names its pointee type and storage class;
- cannot be stored in an aggregate, heap object, buffer, closure, global, or
  host handle;
- cannot be returned or exported;
- cannot cross a suspension;
- cannot outlive the storage operation or verified borrow extent that produced
  it.

Region-member fields do not use ordinary aggregate addresses. Reads, borrows,
takes, initialization, and replacement use region operations so merging,
externalization, finalization state, and resurrection checks cannot be
bypassed.

## Substrate contracts

### Frame storage

A frame-owned environment is stored in the creating runtime activation,
addressed by a stable frame identity plus an environment slot. It must not be
a pointer into a movable Rust `Vec<Frame>` or into a register allocation.

The compiler includes frame-environment teardown in the creating function's
structural cleanup on every exit edge. The environment releases each owning
slot exactly once in reverse slot order. Calling a closure over a frame
environment borrows the environment for the call and performs no retain or
release. A frame-only cell follows the same rule: its generated teardown
destroys its current owning value exactly once when the activation ends.

A runtime identity check traps if malformed bytecode attempts to use a frame
environment after its activation has ended. Valid bytecode cannot trigger that
trap, because selection (rule 3) admits frame storage only when no owning
escape edge was observed.

### Managed buffers

A managed buffer is a target-neutral handle to one control block and one
contiguous element payload. Its semantics include a monomorphic element type,
capacity, per-slot initialized state, an owner count for copy-on-write
sharing, immutable/static versus mutable/dynamic storage, active pin state,
and live/finalizing/dead state. Header layout, pointer width, alignment,
allocation strategy, bitmap representation, and atomicity are target details.
Execution is single-threaded, so owner-count operations need not be atomic; a
later concurrency decision must revisit that.

Zero-capacity buffers are valid and still have a distinct live handle. Bounds,
initializedness, duplicate release of a dynamic owner, use-after-release, and
pin violations fail deterministically. A backend may remove a check only when
it proves the same condition from verified Talk IR.

The bytecode runtime represents a raw pointer as an address plus stable
allocation provenance. Allocation record `N` uses token `N + 1`; token zero
identifies module static memory. Pointer arithmetic and pointer-valued memory
cells preserve the token, so liveness and bounds checks index the owning record
in constant time and then validate the addressed range. Records and tokens are
never reused during a machine run. This is a target representation detail, not
a source-level `RawPtr` escape hatch.

Static buffers, including UTF-8 string literals and generated Unicode tables,
implement the same read interface. They are immutable, never unique, need no
owner-count changes, and are not reported as live dynamic allocations. Static
retain and release are no-ops. Because static storage has no per-owner runtime
state, duplicate static ownership transitions are rejected by MIR and Talk IR
verification rather than detected dynamically.

#### Ownership and views

`Storage<Element>` owns one buffer handle. `Array<Element>` owns a storage
handle, an initialized element count, and a consistent capacity. An owned
`String` owns an immutable `Byte` buffer and a byte count starting at zero.

`Substring`, `UTF8View`, and `Character` are borrowed views of the shape
`borrowed buffer reference + byte start + byte count`. A view does not retain
the buffer and has no destroy glue; its verified source loan keeps the owner
live, and mutation or growth of the owner conflicts with a live shared view.
`Character` is therefore not an integer code point, a runtime scalar, or an
owned mini-string. `Character.to_string()` is the explicit allocation and copy
boundary.

A concrete `Byte` is produced only by a checked read of an initialized slot in
a `Byte` buffer, or by a canonical Byte constant, returning an ordinary Copy
scalar. No `RawPtr` appears in TypedProgram, MIR, or Talk IR to implement a
safe byte read.

#### Operation vocabulary

The target-neutral managed operation vocabulary distinguishes at least:
allocate a buffer of a monomorphic element type and capacity; query capacity;
Copy-read or borrow an initialized slot; move/take an initialized slot leaving
it uninitialized; initialize an uninitialized slot; swap initialized slots;
test uniqueness; retain one owner; begin release of one owner and report
whether final-owner teardown is required; deallocate a finalizing buffer after
every initialized element is destroyed; copy initialized Byte ranges; pin and
unpin a fully initialized Byte range for safe FFI. A generic untyped load,
store, or pointer-add is not an alternative safe representation.

`begin release` consumes exactly one owner. If another owner remains, no
element is destroyed. On the final owner, the payload stays accessible only to
the generated destroy glue until that glue destroys every initialized slot and
deallocates the control block.

#### Copy-on-write order

An O(1) `CheapClone` of a buffer-backed value retains the buffer once and
constructs a second owner; it does not retain or clone each element. Before
mutation:

- a unique dynamic buffer may mutate in place;
- a static or shared buffer detaches into a fresh dynamic buffer;
- detachment clones initialized elements in increasing index order using the
  exact selected element glue;
- a partially built destination is destroyed in reverse initialized order if
  construction cannot complete;
- only after all element clones succeed does the owner replace its old buffer
  handle and release it.

A growing unique buffer allocates the new buffer first, moves initialized
elements in increasing index order, marks old slots uninitialized, commits the
new handle, and deallocates the empty old shell.

Element replacement preserves source assignment order: evaluate the
replacement value; detach if required; take the old initialized element;
destroy it; initialize the slot with the replacement. Array destruction begins
release of its buffer; only the final owner destroys initialized elements, in
reverse index order.

`Array<Element>` may be selected for `CheapClone` only when every possible
detachment can clone `Element` under already selected Copy or CheapClone
evidence. Affine host handles and other non-cloneable resources may be stored
in a unique array, but such an array cannot be cloned.

### Regions and managed members

A region is a merge-only set of managed members:

```text
ManagedMember
  HeapObject
  ClosureEnvironment
  Cell
```

All member kinds share region identity, external-root counting, merge-only
internal edges, deterministic finalization, resurrection checks, and bulk
freeing. Balance reports keep member kinds distinguishable.

#### Roots and merging

Every heap allocation starts one fresh region and one external root. External
roots are heap references, closure values, or cell references owned by stack
storage, globals, value aggregates, parameters or results with owned transfer,
and other admitted non-member storage.

Storing a member reference into a member field makes it internal:

- the target and referenced regions merge;
- the store consumes one owned reference operand; an lvalue source first uses
  a checked Alias edge, while an rvalue may move its existing root;
- internalization releases that consumed external-root obligation after the
  merge, so the internal edge adds no external root;
- a borrowed reference cannot be stored directly as an owning field;
- overwriting or removing the edge does not split the merged region;
- all other external-root counts and members are preserved.

This applies uniformly: an object field holding an object, a closure
environment slot holding a captured closure, and a cell holding a closure all
merge regions the same way. Recursive and mutually recursive local closures
therefore share one region with their cells and do not form an independently
managed graph.

Inline tuples, records, structs, and enum payloads stored in a member field
are walked by exact generated internalize glue so nested member references
merge as internal edges and their consumed external-root obligations end
exactly once. Region finalization does not release those internal references
again. Display names and backend scans are not substitutes for that glue.

Internalization and externalization are transactional, with a read-only
preflight followed by an infallible commit:

1. recursively enumerate every nested member reference and consumed root;
2. validate all handles, source root obligations, region states,
   repeated-reference multiplicities, count arithmetic, destination field
   state, and the complete merge plan without changing region membership,
   field state, source state, or any root count;
3. only if every check succeeds, commit all region merges and end all consumed
   roots; no commit step can fail.

A failed preflight preserves the destination field, every source operand,
region membership, and all root counts exactly. Because merged regions cannot
split, an implementation that mutates during preflight cannot satisfy this
contract.

Taking a member field into external owned storage performs the inverse
transition with the same preflight/commit discipline: enumerate every internal
reference that becomes an external owner; validate without mutation; then
acquire every required external root and clear the field as one infallible
commit before publishing the external value. Buffers, host handles, and other
uniquely owned components transfer without duplication. After commit, ordinary
external Destroy glue owns the acquired roots. A direct Move from internal
storage without this transition is invalid.

Destroying or replacing a value that remains in a member field uses
`Destroy(type, RegionInternal)`: it skips internal member references while
still destroying buffers, host handles, and other owned components. Using
ordinary external Destroy glue there would double-release roots ended by
internalization and is a verifier error.

A region begins teardown when its external-root count reaches zero. This is
not a tracing or trial-deletion cycle collector: regions only merge and can
retain members longer than graph reachability strictly requires while any
external root into the merged region remains. This retention is the accepted
cost of the model; the answer to it is lexical allocation handlers (deferred
below), not region splitting.

#### Construction states and teardown

Every heap record has an explicit construction state:

```text
Allocated        record exists; no field is initialized and it is unpublished
Initializing     a recorded subset of fields is initialized
FullyInitialized all required fields are initialized and the reference may publish
FinalizingHooks  hook phase is active
FinalizingFields field phase is active
Dead             storage is inaccessible
```

Each successful field initialization records its completion before another
field begins. Construction publishes the reference only at `FullyInitialized`.
If construction traps, the object itself receives no direct hook, but each
already initialized field remains an ordinary completed value whose nested
hooks and structural cleanup must run. Uninitialized fields are never read,
hooked, or destroyed.

When the final external root is released, teardown has two separate phases:

1. mark every record in the complete merged region as `FinalizingHooks` before
   running user code;
2. visit records in reverse successful allocation order with exact run-hooks
   glue:
   - for a record that entered teardown fully initialized, invoke its selected
     direct hook;
   - for fully and partially initialized records, recursively run internal
     RunHooks for each initialized inline value field in reverse
     completed-initialization order;
   - throughout this phase every initialized member field remains initialized
     and readable, including fields reached through a cycle;
3. after all region-visible hooks return, mark every record
   `FinalizingFields`, then visit records in the same reverse allocation order
   with exact after-hooks glue; destroy only initialized fields, in reverse
   completed-initialization order, using `DestroyAfterHooks(RegionInternal)`;
4. after all structural field destruction completes, mark records `Dead` and
   bulk-deallocate the region.

No region-visible hook runs after field destruction begins. The readable-field
promise applies to the hook phase only. Phase-two glue is verifier-proven
incapable of dispatching a hook that phase one already ran.

Closure environments and cells have no user hooks; their generated teardown
destroys buffer-owning, generic, and other owned slots exactly once, and their
internal member edges are finalized by the merged region rather than released
as external roots. Environment teardown is generated MIR, not a runtime type
table; generic slots use the drop witnesses stored in the same environment.
The runtime schedules generated finalizers through the region finalization
mechanism; it does not interpret Talk types or choose destruction operations.

Managed buffers remain an independently owned graph. If a member field's
buffer release is not final, its elements survive and receive no hooks. If it
is final, element hooks may run during buffer destruction, subject to the
model boundary on buffers containing member references (below).

A deinit-created independent object starts a fresh region and may tear down
nested inside the current hook when its own last root is destroyed.

Resurrection is forbidden. A reference into a finalizing region cannot become
a new external root, escape from a hook, or be stored into another region.
Member field writes are forbidden while their region is finalizing.
Statically visible escapes are MIR ownership errors; dynamic attempts trap
deterministically. Deinit-local aliases of the current object are teardown
views, not roots. Duplicate root release, access to a dead member, or a store
involving a finalizing region is a deterministic runtime error.

The old runtime implementation may be reused only after a separate adapter
audit proves that it implements this contract behind the new Talk IR
operations.

### Host handles

A host resource is an opaque target-neutral handle class supplied by a stable
host import contract. Creation returns one owned affine handle. Move transfers
it. Duplication is available only when the host contract publishes an explicit
clone operation. There is no implicit host-handle reference count.

Generated destruction uses one exact non-discontinuing core operation with the
signature `(OwnedHostHandle) -> Unit`. It exposes no user effect. The
operation atomically consumes and marks the handle closed before invoking the
host adapter. A host failure is a deterministic runtime error and the handle
remains closed; cleanup never retries it or restores an owned handle. The host
adapter must remove the handle from the live-resource ledger even on that
failure.

An explicit source `close` is separate. It may expose IO and return a checked
failure value, but it consumes the handle, so later generated cleanup has no
handle to destroy. Borrowed host handles never close the resource. Owned and
borrowed policies are part of the import signature and cannot be selected by a
backend-local name switch. Host callbacks cannot retain a lent buffer pointer
or borrowed handle unless a separate source-visible ownership transfer
operation says so.

Strict-linear host handles in heap objects, CoW buffers, closures, and
existentials remain a model boundary. The model admits affine handles whose
deterministic destroy path is representable by generated glue.

## Closure environments and cells

This section is rule 3 applied to function values.

### Storage classes

```text
EnvironmentStorage
  Empty   the closure captures no runtime values; the degenerate zero-slot
          case of Frame, kept distinct so captureless closures allocate nothing
  Frame   the environment is owned by the creating activation
  Region  the environment is an owning member of a managed region
```

A closure value is a small pair of code identity and an environment reference:

```text
ClosureValue
  chunk: ChunkId
  environment: Empty | Frame(FrameIdentity, EnvironmentSlot)
                     | Region(ManagedMemberId)
```

`EnvGet` reads through that reference. Direct calls continue to use `Empty`.

### Online selection

Each closure construction receives an `EnvironmentId`. Its slot facts are
fixed at construction - the ordered checked capture operations, inherited
generic evidence, and the source origins of non-owning slots. Effect handlers
are resolved at invocation and occupy no environment slot (ADR 0051). Its storage is a one-bit latch initialized to `Frame` (`Empty` when
there are no slots) and set to `Region` when an owning sink is observed. The
latch never moves back. `MakeClosure` and environment operations refer to
`EnvironmentId`, so lowering reads the final latch directly. This is not a
second traversal and not general backpatching: the only mutation is the latch.

MIR values carry environment provenance - a set of `EnvironmentId`s, since
aggregates and outer closures may contain several closure values - during the
same construction walk that currently carries `anchored_closures`:

- `MakeClosure` defines its own environment provenance and inherits the
  provenance of closure values captured in its slots;
- `Copy` propagates provenance to its destination;
- tuples, records, variants, existential packages, and other value aggregates
  union operand provenance into their destination instead of treating
  aggregate construction itself as an escape;
- `SetField` on a local value propagates source provenance into the updated
  local;
- `Goto` propagates argument provenance to block parameters;
- branch joins union provenance conservatively.

An owning lifetime sink sets the latch on every environment in the operand's
provenance:

- return from the creating activation;
- global storage;
- object or raw managed storage;
- finalizer storage;
- an owning or consuming call argument whose contract permits retention;
- abort delivery across the creating activation;
- any boundary whose checked ownership contract is unavailable.

A checked borrowed/noescape argument is not a sink. Calls use the checked
argument operations published through `TypedProgram`; MIR does not reconstruct
the decision from source markers or runtime representation. Inlining after
selection keeps the conservative choice; it never invalidates it.

Cell storage is conservatively a sink for closures sharing that cell. A cell
may remain frame-local only when online provenance proves that both the cell
and every closure sharing it remain in the activation. A cell reachable from a
`Region` environment is a region member; storing a closure back into that cell
merges the two regions.

In-place mutation that the online tracker cannot summarize safely is
conservative: affected environments become `Region`. More precise tracking may
be added inside the builder only when it removes a measured allocation and
does not add another body pass.

### Slot ownership

Every environment slot is owned exactly as its checked published operation
describes: a Copy capture stores the copied scalar or aggregate; a snapshot
capture retains once at environment construction; a consuming capture
transfers ownership into the environment; an owning stored view retains its
referent according to the checked promotion operation; a shared or exclusive
borrowed capture owns nothing and records its source lifetime; inherited
generic evidence uses its published ownership contract; a cell slot carries
the cell's managed member handle. Frame and
region environments own the same slots the same way; the storage class changes
where generated teardown runs, never the operation.

### Borrowed captures

Heap allocation does not make an arbitrary borrowed capture safe. When
selection sets a latch to `Region`, every borrowed slot must have one of these
checked dispositions:

1. its lifetime is proven to include the escape extent under a named language
   rule;
2. typing selected an owning stored-view promotion, and environment
   construction performs that promotion; or
3. the program is rejected with a structured borrow-escape diagnostic carrying
   the capture and sink origins.

MIR does not silently retain an exclusive borrow, convert aliasing semantics,
or reinterpret a capture mode to make promotion possible. Owned snapshots and
consuming captures are the valid behavior that removes the current
`anchored_escape` capability rejection. Genuine invalid borrowed escapes
remain ownership errors.

### Aggregates and nesting

Constructing an aggregate is not itself proof of escape; a tuple of closures
used entirely within one activation may retain frame environments. Provenance
is transitive: if an outer closure escapes, the environments of closures it
captures become region-backed, however deeply nested in tuples, records,
variants, or existentials.

## Ordinary value cleanup and generated glue

Cleanup follows ADR 0032: values are destroyed in reverse
completed-initialization order. The lowerer emits one monomorphic generated
function per demanded glue identity, distinguishing at least:

```text
Clone(type, selected witnesses)
RunHooks(type, ExternalOwned | RegionInternal, selected witnesses)
DestroyAfterHooks(type, ExternalOwned | RegionInternal, selected witnesses)
Destroy(type, ExternalOwned | RegionInternal, selected witnesses)
BufferDetach(type, selected witnesses)
Internalize(stored type)
Externalize(stored type)
EnvironmentTeardown(environment layout, selected witnesses)
```

Glue identity is semantic metadata, not a debug name. Talk IR verification
checks the role, storage mode, monomorphic type, signature, selected callees,
and call sites. A backend executes the body and may not reconstruct ownership
from a type layout.

Ordinary `Destroy(mode)` preserves ordinary value semantics: invoke the
nominal's direct hook, then destroy initialized fields in reverse order, each
nested field's own Destroy running its hook immediately before its structural
teardown. It is not a region-wide hooks-first prepass. `RunHooks` and
`DestroyAfterHooks` are the exact split used only where a two-phase owner - a
region - requires all region-visible hooks before structural destruction.
`RunHooks` recursively invokes selected hooks of fully initialized inline
value instances; MIR verification guarantees those hooks cannot deinitialize
their teardown views. `DestroyAfterHooks(ExternalOwned)` releases member roots
recursively as well as destroying buffers, host handles, and other owned
fields. `DestroyAfterHooks(RegionInternal)` skips member-root release because
internalization already ended those obligations. The storage modes and
hook/after-hook roles are not interchangeable.

For a nominal value with a user `Deinit` conformance, generated Destroy glue
invokes the selected hook exactly once; the hook's `self` and aliases derived
from it are teardown views of that same instance and do not redispatch the
hook; after the hook returns, Destroy processes each still-initialized field
in reverse completed-initialization order; the glue then deallocates owned
storage, if any. The hook may read fields and create unrelated values; it may
not move, take, destroy, or deinitialize storage through its teardown view,
and that view may not escape. The generated caller remains the sole structural
teardown owner. Cleanup may not expose an unhandled user effect under ADR
0032. A newly created sibling value is a distinct instance and receives its
own hook.

## Global destruction schedule

Every linked executable with resource-owning globals has one explicit global
destruction schedule derived from its verified initialization schedule. It is
part of Talk IR, not a backend convention.

- Each successfully initialized global is recorded exactly once and owns one
  canonical runtime initialized bit.
- Every destruction action is `DestroyGlobalIfInitialized(global, destroy)`:
  it tests the bit, atomically clears it before entering user or host cleanup,
  calls exact external Destroy only when the bit was set, and otherwise
  performs a verified no-op.
- Destruction visits only completed initializations, in exact reverse of their
  completed initialization order. Because linking initializes suppliers before
  consumers, reverse destruction destroys consumers before suppliers; within a
  module it reverses the producer-published source declaration order.
- Literal/static globals with no owned dynamic resource have a verified no-op
  action rather than an inferred backend exemption.

Moving an owned resource out of global storage is not permitted. A result or
local derived from a global must borrow, use checked Alias, or use a selected
clone. Mutable-global replacement evaluates its RHS, invokes the guarded
destroy action for the old value, stores the replacement, and sets the
initialized bit. An explicit early destroy uses the same guard and leaves the
global uninitialized until a later explicit initialization permitted by its
mutability contract.

After the selected entry returns, its owned result is first materialized in
the harness's result-owner storage - a real ownership transfer, independent of
the globals. The runtime then executes the global destruction schedule before
returning the result or measuring its transitive footprint. Destroying the
result afterward must reduce the remaining live footprint to zero.

A runtime trap follows an explicit failure-cleanup path: generated cleanup for
initialized values in active frames, then every completed global in the same
reverse guarded schedule, then the primary trap report and balance snapshot.
If an initializer traps before its result is stored, that global's bit remains
clear. A second trap during cleanup terminates teardown with a deterministic
`trap during cleanup` error and a balance-at-trap report. Talk IR operations
that can dynamically trap while managed resources are live must expose an
explicit failure successor or equivalent verified cleanup edge.

## FFI pinning

Safe FFI obtains an address only through a scoped pin over a fully initialized
range of a managed `Byte` buffer. Arbitrary `Element` buffers are not safely
pinnable: their payload may contain uninitialized slots, padding, member
references, host handles, or a target-specific representation. Widening safe
pinning requires a later accepted FFI-safe representation class.

Pinning validates the complete Byte range, then returns a non-storable
pinned-address capability and an affine pin token consumed by unpin on every
finite path. During the pin:

- the control block and payload address remain live and stable;
- immutable pins may coexist, and ordinary buffer retain may create another
  CoW owner while immutable pins are active;
- a mutable pin requires a unique dynamic buffer and exclusive source loan;
- buffer retain is forbidden while a mutable pin is active;
- detach, growth, final-owner release, deallocation, and conflicting mutation
  are forbidden; a non-final owner release during immutable pins is permitted;
- the address and token cannot be returned, stored, captured, serialized, or
  carried across user-effect suspension.

A pin does not change the buffer owner count. Runtime pin state prevents final
release or relocation even if malformed target code attempts it; MIR and Talk
IR verification still require unpin before the source owner can die. Static
Byte ranges may be pinned immutably and never mutably. `withUnsafeBytes` and
`withCString` express this with a nonescaping callback; they do not return a
pointer. `withCString` first provides a fully initialized, NUL-terminated Byte
range; the pin operation does not invent a terminator.

Heap object layout is not pinnable or FFI-visible. A heap object may be passed
only as an opaque host token through an explicit adapter.

## The `'alloc` effect

`'alloc` remains an inferred core effect supplied by the runtime's implicit
core handler; it is not user-handleable. Lexical allocation handlers, custom
arenas, and region polymorphism are deferred source-language work (see
boundaries). A future custom allocation handler must preserve the managed
operation semantics of this ADR or introduce a new accepted contract.

## Talk IR boundary

Talk IR owns semantic operation identity and ordering. It must represent:

- managed-buffer and heap-reference types distinct from raw addresses;
- buffer slot initializedness operations;
- explicit buffer retain, final-owner release, and deallocation;
- explicit root acquire/release, region merge, and transactional
  internalization/externalization preflight and commit;
- unpublished construction state, initialized-field state, and publication
  only after full initialization;
- member allocation with separate exact recursive-hook and after-hook
  field-destruction identities;
- external-owned versus region-internal and hook versus after-hook Destroy
  roles;
- empty, frame, and region environment construction, with the selected storage
  class, environment layout width, and generated teardown chunk where
  required - not source capture modes or types;
- scoped Byte-range pin and unpin;
- generated glue roles and exact calls;
- opaque host handle types and stable host imports;
- the initialized-bit-guarded global destruction schedule and
  managed-operation failure-cleanup edges.

Target adapters own control-block and object-header layout; pointer width,
alignment, and ABI; buffer owner-count storage; region union-find or an
observationally equivalent implementation; finalizer dispatch tables and
calling convention; pin representation; host API handles and platform error
conversion.

A backend may choose any data structure that preserves the operation
semantics, ordering, traps, and resource counts. It may not scan source types
to discover fields, infer cleanup from liveness, or map a display name to a
runtime function.

## Cross-artifact laws

### Representation law

`NominalRepresentation::Value` remains a value aggregate even when one of its
fields is a heap reference. `NominalRepresentation::Heap` lowers to exactly
one heap-object type and heap-reference representation. Representation does
not become contagious through fields.

### Alias and root law

Every source heap duplication has one checked Alias edge selected by context,
never by liveness. Structural Alias evidence for a nominal also proves that
its lifecycle is trivial. Every verified Alias edge produces exactly one
external-root acquire per represented member reference. Move between external
owners produces none and borrow produces none. Internalization consumes its
owned operand by merging and ending that root. A take from internal storage
first externalizes and acquires each nested root before clearing the field.
External Destroy releases those roots; internal Destroy does not. No target
adapter invents alias, internalization, or externalization edges.

### Root-transition transaction law

Internalize and Externalize perform complete read-only preflight before any
region, root-count, field-state, or source-state mutation. A failed preflight
leaves all four unchanged. After success, commit is infallible and publishes
no intermediate state.

### Selection law

Substrate selection happens once, inside MIR construction, per rule 3. The
selected storage class is trusted compiler output when produced in-process and
validated structure when loaded from bytes. Validation never re-runs
selection. Conservative uncertainty may cost a region allocation; it may never
change an ownership answer.

### Environment law

Frame and region environments own the slots their checked capture facts
describe, release each owning slot exactly once, and differ only in where
teardown runs. Copying an owned region-closure reference acquires a region
claim; destroying it releases the claim; the last claim runs the generated
environment teardown and frees the member.

### View erasure law

Every `Substring`, `UTF8View`, and `Character` reference in Talk IR derives
from a verified MIR loan. Erasure adds no retain and no escape. The same
source range and byte range reach buffer operations.

### Buffer initialization law

MIR ownership of elements and Talk IR buffer slot state agree: initialize
targets an uninitialized slot, read/take targets an initialized slot, take
uninitializes it, and final-owner destruction visits each remaining
initialized slot exactly once.

### Glue identity law

The selected clone and Deinit witnesses, monomorphic type, field order, and
generated glue identity are preserved exactly from CheckedMir through Talk IR.
A glue call cannot be replaced by another function with a compatible display
name or signature.

### Cleanup order law

Source reverse-initialization cleanup order reaches generated glue unchanged.
CoW detachment, replacement, two-phase region teardown, frame-environment
teardown, nested finalization, global destruction, trap cleanup, and
discontinue paths preserve the ordering defined above. Region-visible hooks
complete while member fields remain initialized; only then may after-hook
internal field destruction begin. Partial records run no direct object hook
and process only their initialized fields.

### Region boundary law

Only explicit root operations affect the external-root count. Only explicit
internalization/merge operations create region edges. A backend scan, garbage
collector root guess, or raw pointer store cannot alter the answer.

### Pin and host ownership law

Every safe pin covers a fully initialized Byte range and has one unpin on each
finite path. A mutable pin cannot coexist with a buffer retain. Every owned
host handle has one close, transfer, or accounted result owner. Generated host
destruction is a non-discontinuing core operation that consumes the handle
before host failure can be reported. Borrowed handles and addresses perform
neither action.

### Global lifetime law

The global destruction schedule is exactly the reverse of completed linked
initialization. Every action is guarded by the global's canonical initialized
bit and clears it before cleanup. Result ownership is established before the
schedule runs. Success and primary runtime-trap paths run the same guarded
completed-global schedule; no backend supplies process-exit or module-order
semantics implicitly.

### Fail-closed law

A generic, existential, closure, buffer, host, or region combination outside
the model boundaries rejects before partial lowering. Raw pointers cannot be
used as a fallback representation for safe managed operations.

## Verifier obligations

### TypedProgram validation

- Heap aliases carry exact structural Alias evidence and are selected by the
  contextual rule without last-use information.
- Nominal structural Alias evidence proves no user Deinit hook, custom
  lifecycle, hidden storage, or omitted field; a lifecycle-bearing nominal
  requires Copy/clone authority or Move.
- Consuming arguments, owned returns, explicit transfers, ordinary owning
  assignments, aggregate fields, and member-field initializations publish the
  required Move, Alias, or Borrow edge exactly once.
- Heap declarations cannot claim `Copy` or `CheapClone`.
- Selected buffer clones prove every future detachment can clone the element.
- Capture operations and inherited evidence publish their ownership contracts;
  borrowed captures publish their source lifetime.
- Borrowed views cannot appear in owned fields, globals, or escaping captures.
- Unsafe/FFI ownership policies and nonescaping callback shape are explicit.

### CheckedMir verification

- Alias, external Move, borrow, clone, both Destroy modes, internalization,
  externalization, and root ownership agree on every CFG path.
- Internalize and Externalize preflight every nested reference and transition
  without mutation; failed preflight preserves source, field, regions, and
  root counts, while successful commit is infallible.
- A take from region-internal storage acquires every nested root before
  clearing the field; internal destruction skips those roots but still
  destroys other resources.
- Environment provenance propagates through copies, aggregates, block
  parameters, and joins; every latch set to `Region` is justified by an
  observed owning sink; every borrowed slot in a region environment has a
  checked disposition or a structured borrow-escape diagnostic.
- Construction tracks Allocated, Initializing, FullyInitialized, both
  finalizing phases, and Dead; partial cleanup visits only initialized fields
  and omits the incomplete object's direct hook.
- Region hook traversal recursively runs initialized inline value hooks, and
  phase-two DestroyAfterHooks cannot redispatch them.
- Buffer slot initialization and element ownership agree at each operation.
- Replacement and detachment order is structural.
- Every pin covers a fully initialized Byte range, every pin token is
  unpinned on every finite normal, early, trap-cleanup, and discontinue path,
  and no pinned address crosses suspension or escape.
- Mutable pins prove uniqueness and reject retain or sharing while active.
- Deinit teardown views cannot escape or move, take, destroy, or deinitialize
  their storage; region finalization views obey the same rule and obvious
  resurrection is rejected.
- Combinations outside the model boundaries reject.

### Talk IR verification

- Managed operation arity and operand/result types are exact.
- Buffer and region operations cannot be performed through generic addresses.
- Generated glue roles, storage modes, hook/after-hook behavior, and exact
  signatures are unique per demanded identity.
- Member allocation registers separate matching monomorphic recursive-hook and
  after-hook field-destruction glue plus explicit construction state.
- Internalize and Externalize glue recursively agree on every inline member
  reference in the stored type and expose preflight/commit semantics.
- Environment construction names its storage class, layout width, and
  generated teardown identity; region environments name a valid generated
  teardown.
- Final-owner buffer paths destroy each initialized element before
  deallocation.
- Pin tokens dominate Byte-address uses and are consumed once on every finite
  path; mutable pin paths contain no retain.
- Host imports have stable identities and exact ownership/effect signatures.
- The global destruction schedule contains each initialized resource-owning
  global exactly once in reverse initialization order, every action uses and
  clears the canonical initialized bit, and failure edges reach it after
  active-frame cleanup.
- Raw addresses, target-specific runtime names, and unverified layout
  constants do not appear.

### Backend validation

- Encoded operations, indices, types, glue references, and control targets are
  valid before execution.
- Referenced chunks and environment slots exist; frame-environment operations
  occur only in chunks that declare the matching layout; environment accesses
  stay within the declared width; malformed storage tags or handles are
  rejected before execution.
- Dynamic bounds, initializedness, owner-count, region-state, pin-state,
  frame-identity, and host-handle failures return deterministic errors rather
  than panicking or executing unchecked.
- Root-transition preflight performs no mutation and target commit cannot
  fail; object and global initialized-state guards match verified Talk IR.
- A backend claiming the R1 profile reports the complete and exact resource
  balance below; an inexact result footprint rejects the profile.

## Resource oracles

Every successful R1 fixture reports:

```text
live dynamic buffer allocations
live initialized buffer elements
live heap objects
live closure environments
live cells
live regions, including finalizing regions
live pins
live owned host handles
result-owned footprint for each category
```

All live counts must equal the exact transitive footprint intentionally owned
by the returned result; member kinds stay distinguishable in the report. A
backend that cannot compute that footprint exactly rejects the result or
remains outside the R1 profile. After the harness destroys that result, every
count is zero. Static buffers are reported separately and do not count as
leaks. No resource exemption is anonymous: a temporary unsupported case has a
parity ledger row and removal condition.

Required oracle cases include:

- shared buffer clone then last-owner destruction;
- detach and mutate while the original remains unchanged;
- grow by moving unique elements;
- replacement destroys the old element before initialization;
- nested arrays and reverse-index element cleanup;
- structural Alias of a lifecycle-trivial value product and rejection of the
  same shape with a nominal Deinit hook;
- direct heap cycle teardown;
- failed multi-reference Internalize preflight preserving all regions and root
  counts, followed by successful infallible commit;
- failed multi-reference Externalize preflight preserving field state and root
  counts, followed by successful infallible commit;
- internal aggregate extraction through Externalize;
- internal aggregate replacement and teardown through internal Destroy;
- interior heap alias returned from a merged region;
- heap objects with managed-buffer fields;
- partial construction destroying only initialized fields without the
  incomplete object's direct hook;
- two-phase reverse-allocation direct and nested inline hooks followed by
  after-hook field destruction;
- a captureless function value allocating no environment;
- an immediately called capturing trailing block using a frame environment;
- a closure passed through a checked borrowed argument remaining frame-backed;
- returning a closure over a managed `String` selecting a region environment,
  executing after the creator returns, and freeing exactly once;
- a closure stored in a global, object, existential, and returned aggregate
  selecting a region environment;
- a local aggregate containing closures not forcing region allocation until
  the aggregate reaches an owning sink;
- copies, branches, and block-parameter joins preserving environment
  provenance;
- an escaping outer closure promoting environments of captured inner closures;
- consuming and snapshot captures balancing on normal return, early return,
  resume, and discontinue;
- generic owning captures invoking the stored drop witness exactly once;
- an escaping borrowed capture reporting the capture and escape sink as a
  structured diagnostic;
- independent recursive closure/cell groups tearing down without leaks;
- closure/cell cycles merged with heap objects finalizing and freeing as one
  region;
- a runtime identity check rejecting a malformed call through a dead frame
  environment;
- linked global teardown in consumer-before-supplier order after result
  ownership transfer on success;
- conditional early global destroy followed by a guarded final no-op;
- initializer trap destroying only the completed initialization prefix;
- primary entry trap running active-frame cleanup and the guarded global
  schedule;
- nested teardown;
- resurrection trap with a balance-at-trap report;
- immutable and mutable Byte-range pins on every exit path, including retain
  rejection during a mutable pin;
- static buffer ownership transitions verified without runtime owner tokens;
- host close, transfer, destroy failure after close, duplicate-close
  rejection, and result ownership;
- bytecode encode, decode, and validation preserving the selected environment
  storage class.

Tests assert allocation class through counted runtime instrumentation, not by
matching disassembly or relying on optimizer behavior.

## Model boundaries

These combinations are outside the model. They reject at checked-fact level
before partial lowering; they are boundaries, not phases, and each names the
design work that could admit it:

- existential payloads containing member references, and existential cycles
  (needs root/internal-edge conversion through existential packages);
- managed buffers whose element type contains a member reference when that
  buffer would be stored in a region, and buffer-mediated cycles (needs
  buffers brought into the region hook prepass);
- member references in opaque or unsafe raw storage;
- weak or unowned member references;
- strict-linear resources inside region members or shared buffers;
- host-mediated cycles and host-retained callbacks;
- addresses or pins across effect suspension;
- user-handled allocation effects, lexical arenas, and region polymorphism
  (the intended relief for merge-only retention; see rule 3 and research);
- concurrent sharing and atomic buffer owner counts;
- general tracing or trial-deletion cycle collection;
- unsafe arbitrary pointer arithmetic and typed raw-memory loads/stores;
- resurrection.

## Alternatives rejected

### Uniform reference counting

Rejected (ADR 0029, confirmed). Buffer CoW counts and region external roots
are purpose-specific. Value aggregates, unique affine values, frame
environments, and host handles do not acquire a universal count. Interpreter
register copies would change Rust strong counts without Talk ownership
operations, and Rust `Drop` cannot execute generated MIR with generic
witnesses and deterministic effect-unwind ordering.

### Region storage for every capturing closure

Rejected. It allocates and updates region claims for synchronous trailing
blocks and local closures that provably die with their activation. The builder
already observes enough flow to avoid that cost without another traversal.

### A separate escape-analysis pass

Rejected. It adds a whole-body stage, duplicates flow already observed by MIR
construction, and conflicts with ADR 0034's staging criteria. Online selection
makes the same conservative decision while the builder emits the relevant
edge.

### A frontend `escapes` bit

Rejected. Escape-based storage selection is runtime representation and CFG
flow, owned by MIR under ADR 0038. Making typing's answer load-bearing for
allocation would create a second code-generation authority and would violate
rule 4.

### Dynamic promotion from frame to region storage

Rejected. Existing aliases would need forwarding or rewriting, consuming and
linear captures would need transactional ownership transfer, and promotion
across branches and unwind edges would introduce runtime state and failure
modes. The latch chooses one representation per site before bytecode emission.

### A separate closure reference-counted heap

Rejected. It duplicates external-root accounting, finalization, resurrection,
cycle handling, diagnostics, and balance instrumentation already provided by
regions. Closure and cell edges must compose with heap objects in one graph.

### Tracing GC for cycles

Rejected. It does not by itself provide deterministic hook timing or
reverse-allocation order, and it is unnecessary for the direct object and
closure/cell cycles that merge-only regions already admit.

### Raw pointers as Talk IR managed values

Rejected. They lose ownership class, bounds, initializedness, pin state,
backend independence, and safe FFI lifetime information.

### Borrowed views that retain buffers

Rejected. It duplicates source borrow semantics at runtime, changes CoW
uniqueness, and permits a borrow-checker error to become an accidental owned
escape. Verified source loans are the authority.

### Reuse the old runtime contract unchanged

Rejected. It would make object indices, byte-vector addresses, region ledger
quirks, and finalizer-pump control flow compiler contracts. Reuse is permitted
only behind the semantic operations adopted here.

## Research and precedent

- Gay and Aiken, *Language Support for Regions*, PLDI 2001: region reference
  counting and region lifetime as the basis for merge-only ownership regions.
- Arvidsson et al., *Reference Capabilities for Flexible Memory Management*,
  OOPSLA 2023: explicit capability-controlled memory management and
  deterministic region finalization as the modern comparison point.
- Tofte and Talpin, *Implementation of the Region Inference Calculus*, TOPLAS
  1997: the static, lexical, inferred alternative to this model's runtime
  regions. Region inference would unify substrate selection into typing but
  requires whole-program inference and region polymorphism, both excluded by
  ADR 0034; merge-only retention is the accepted cost of that exclusion.
- Choi et al., *Escape Analysis for Java*, OOPSLA 1999, and Blanchet, OOPSLA
  1999: the NoEscape/ArgEscape/GlobalEscape lattice that Empty/Frame/Region
  specializes; checked argument contracts replace interprocedural escape
  summaries.
- Kranz et al., *Orbit: An Optimizing Compiler for Scheme*, SIGPLAN 1986:
  per-closure-site representation choice by analysis.
- Morrisett and Harper, *Typed Closure Conversion*, POPL 1996: generated
  per-shape environment teardown instead of a runtime type table.
- Rust's `std::pin` contract and Swift's scoped `withUnsafeBytes` APIs: a
  pinned pointee remains valid at one address through the pin lifetime;
  unsafe addresses are lent to a nonescaping operation.
- Rust MIR drop elaboration and Swift Ownership SSA, as cited by ADR 0032:
  initializedness and consuming operations are structural IR facts, verified
  before target lowering.

## Supersession record

This ADR consolidates and supersedes:

- **ADR 0033** in full. The P7 acceptance record carries to the consolidated
  text: distinct substrate policies; the contextual checked Alias edge and
  lifecycle-trivial structural evidence; transactional
  internalize/externalize; both Destroy storage modes and hook/after-hook glue
  identities; partial construction and two-phase teardown; guarded global
  destruction; no resurrection; scoped Byte pinning and non-discontinuing host
  destruction; the Talk IR boundary; exact verifier and oracle completeness.
  The single semantic change is that the boundary items "escaping closure
  environments that capture heap references" and "closure/cell cycles" are
  admitted by the model rather than rejected, per ADR 0040's design.
- **ADR 0040** in full. Its storage classes, online selection, borrowed-
  capture dispositions, and aggregate provenance appear here as rule 3 and
  the closure environments section, with the mutable-plan framing simplified
  to a one-bit latch and the function-boundary sink rule stated explicitly.

Unchanged neighbors: ADR 0034 (staging and interface depth), ADR 0037 (the
unsupported-site work program, which now points its closure mechanisms at this
ADR), ADR 0038 (authority boundaries). The G0 contract stack obligations from
ADR 0033 - adding Alias to TypedProgram, CheckedMir, validation, verification,
printers, and negative tests - carry forward unchanged.
