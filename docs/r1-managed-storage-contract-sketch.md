# R1 managed-storage contract sketch

Status: accepted design sketch for [ADR 0033](adr/0033-managed-storage-heap-regions-and-ffi-lifetimes.md); not yet a production Rust contract (2026-07-15)

Semantic authority is ADR 0032 together with the accepted decisions in ADR
0033. The shapes below identify the current contract gaps and the smallest
coordinated additions expected for R1. They become production contracts only
through the G0 stack. Exact Rust enum names may change during G0, but the
accepted distinctions may not collapse.

## Shared checked vocabulary

### Heap aliasing

The current `UseMode` cannot represent baseline `'heap` reference aliasing
without pretending it is a user `Copy` conformance or a selected
`CheapClone`. Add a distinct checked edge:

```rust
pub enum UseMode {
    Copy(CopyEvidence),
    Alias(AliasEvidence),
    InvalidCopy,
    InvalidAlias,
    Move,
    BorrowShared,
    BorrowMut,
    Discard,
}

pub enum AliasEvidence {
    HeapReference { structure: ItemId },
    Tuple(Vec<AliasComponentEvidence>),
    Record(Vec<(crate::label::Label, AliasComponentEvidence)>),
    ValueStruct {
        structure: ItemId,
        lifecycle: LifecycleTrivialEvidence,
        fields: Vec<(ItemId, AliasComponentEvidence)>,
    },
}

pub struct LifecycleTrivialEvidence {
    structure: ItemId,
}

pub enum AliasComponentEvidence {
    Copy(CopyEvidence),
    Alias(AliasEvidence),
}
```

`AliasEvidence` proves the exact duplicated type contains only ordinary Copy
components and heap-reference components. It is not conformance evidence and
does not make the type satisfy the source `Copy` protocol. For a nominal value
struct, `LifecycleTrivialEvidence` additionally proves from canonical items that
the nominal has no user Deinit hook, custom clone/destroy lifecycle, hidden
storage, or omitted/reordered field. Its destruction is only the structural
component cleanup represented by the proof. A lifecycle-bearing nominal cannot
publish structural Alias; it needs Copy/selected clone authority or Move.
Enums need a case-specific lifecycle rule before whole-enum Alias is admitted;
R1 may initially admit only the direct heap-reference case and lifecycle-trivial
value products required by real fixtures.

Capture modes do not gain Alias in v1 because escaping heap captures remain
rejected. Passing modes do not gain Alias: an owned result or consumed argument
moves a root, while an ordinary shared parameter borrows it. Alias is a value
use that creates another owning external root.

Selection is contextual, not liveness-based:

```text
borrow parameter/receiver/context        -> BorrowShared or BorrowMut
explicit consume/Consume parameter       -> Move
owned return or explicit transfer        -> Move
ordinary owning place use of heap ref    -> Alias
fresh heap rvalue into owning storage    -> Move
ordinary aggregate duplicate             -> structural Alias
consuming/return aggregate edge           -> Move
```

Local bindings, assignment right-hand sides, value and heap field
initialization, arguments, and returns must all publish the selected edge. A
heap-field destination consumes an Alias or Move operand through
internalization; it does not store a borrow. Moving out of internal heap storage
requires externalization first.

TypedProgram validation rejects `InvalidAlias`, evidence for the wrong nominal
representation, a nominal with lifecycle behavior, omitted value fields,
reordered fields, and evidence that crosses a managed buffer, existential,
closure environment, or opaque type. Adding a Deinit conformance invalidates a
previously constructible lifecycle-trivial proof.

### Canonical managed operation identity

Safe/core storage operations need one checked semantic vocabulary rather than
parser inline-IR payloads:

```rust
pub enum ManagedIntrinsic {
    BufferAllocate,
    BufferCapacity,
    BufferReadCopy,
    BufferBorrowShared,
    BufferBorrowMut,
    BufferTake,
    BufferInitialize,
    BufferSwap,
    BufferIsUnique,
    BufferCopyBytes,
    ByteBufferPinShared,
    ByteBufferPinMut,
    ByteBufferUnpin,
}

pub struct ManagedIntrinsicApplication {
    operation: ManagedIntrinsic,
    element: Ty,
    operands: Vec<ManagedIntrinsicOperand>,
}
```

The operation plus monomorphic element type derives the signature. Type
checking selects it only for trusted core definitions and publishes canonical
operands and types. Unknown memory IR becomes the existing payload-free
`Unsupported` marker. Retain, final-owner release, deallocation, heap root
operations, and generated finalization are lowerer-generated operations and do
not need source-facing TypedProgram cases.

The three pin operations are not generic over `element`: validation requires a
fully initialized `Byte` range. No safe managed intrinsic exposes arbitrary
Element layout to FFI in v1.

The G0 stack must decide whether this extends `CheckedInlineIrOperation` or is a
canonical intrinsic callable item. It may not retain parser instruction kinds,
register spellings, source type annotations, or backend opcodes.

### FFI and host ownership

The later K1 host-import contract needs ownership in the signature:

```rust
pub enum HostHandleMode {
    Owned,
    BorrowShared,
    BorrowMut,
}

pub struct HostResourceClass {
    stable_name: String,
    destroy_import: Option<ExternalCallable>,
    clone_import: Option<ExternalCallable>,
}
```

This is a forward contract sketch only. R1 pinning must not invent host import
names before K1 accepts this part. An accepted `destroy_import` must be an exact
non-discontinuing core `(OwnedHostHandle) -> Unit` operation. Execution consumes
and marks the handle closed before entering the adapter; adapter failure is a
deterministic runtime error and cannot restore or retry the handle. A
source-visible effectful `close` is a separate consuming API.

## TypedProgram impact

The existing item contract already distinguishes
`NominalRepresentation::{Value, Heap}`. R1 additionally requires validation
that:

- a heap declaration cannot publish a `Copy` or `CheapClone` conformance;
- a heap source use that duplicates a reference publishes `UseMode::Alias`;
- structural Alias of a nominal publishes lifecycle-trivial evidence and
  rejects any user Deinit hook, custom lifecycle, hidden storage, or incomplete
  field proof;
- Move, Borrow, or Alias is selected by the contextual matrix above before MIR,
  including bindings, assignments, aggregate and heap fields, calls, and
  returns, without consulting last-use liveness;
- `String`, `Storage`, `Array`, borrowed views, and trusted managed intrinsic
  items resolve to canonical item identities rather than display names;
- an admitted `Array<Element>: CheapClone` selection carries sufficient
  element Copy/CheapClone evidence for detachment;
- `Substring`, `UTF8View`, and `Character` cannot validate in owned fields,
  globals, or escaping captures;
- the deferred heap-containing storage, existential, and closure forms reject
  with source-backed diagnostics.

The source-core migration should replace the current unconditional
`Array<Element>: CheapClone` with a conditional contract. The exact source
predicate spelling is frontend work, but no lowerer may discover the condition
by searching conformances.

## CheckedMir impact

### Alias operand

Preserve the checked alias edge separately from Copy and Move:

```rust
pub enum OperandKind {
    Constant { value: Constant, ty: Ty },
    Copy { place: Place, evidence: CopyEvidence },
    Alias { place: Place, evidence: AliasEvidence },
    Move(Place),
    Borrowed { place: Place, loan: LoanId },
    Function(ItemId),
}
```

MIR verification checks Alias evidence against the exact place type. Alias does
not deinitialize the source and creates a new external-root cleanup obligation
for the destination. Move transfers a root only when its source is already
external. A heap-field take must externalize before clearing the field; it is
not represented as an ordinary Move. Copy and Alias evidence both end after MIR
verification; the lowerer sees the explicit operation and concrete
representation, not the proof tree.

### Managed storage operations

The MIR vocabulary must keep ownership transitions structural. One possible
shape is:

```rust
pub enum ManagedRvalue {
    AllocateBuffer { element: Ty, capacity: Operand },
    BufferCapacity { buffer: Operand },
    BufferReadCopy { buffer: Operand, index: Operand, evidence: CopyEvidence },
    BufferBorrow {
        buffer: Operand,
        index: Operand,
        permission: BorrowPermission,
        loan: LoanId,
    },
    BufferTake { buffer: Operand, index: Operand },
    BufferIsUnique { buffer: Operand },
}

pub enum ManagedStatement {
    BufferInitialize { buffer: Operand, index: Operand, value: Operand },
    BufferSwap { buffer: Operand, lhs: Operand, rhs: Operand },
    BufferCopyBytes {
        source: Operand,
        source_start: Operand,
        destination: Operand,
        destination_start: Operand,
        count: Operand,
    },
    PinByteRange { /* initialized range, token/address, permission */ },
    UnpinByteRange { token: Operand },
}
```

`BufferReplace` is intentionally absent from the semantic minimum. MIR emits
Take, Destroy, then Initialize so assignment order cannot be hidden in one
backend operation.

Heap construction and field operations may use dedicated MIR forms or checked
aggregate operations carrying `NominalRepresentation::Heap`. Whichever shape is
chosen must distinguish:

- allocation of a fresh heap object;
- Copy-read versus Alias-read versus borrowed field access;
- field take, initialize, and replacement;
- internalization of inline nested heap references, consuming an Alias-created
  or moved external-root obligation after merging;
- externalization before field take, recursively acquiring external roots
  before the field is cleared;
- external-owned and heap-internal destroy modes, with the latter skipping
  internal heap references while still destroying buffers and host handles;
- rejection of a borrowed reference stored directly into an owning heap field;
- mutation while finalizing as a forbidden runtime state.

Heap construction has explicit state rather than treating allocation as a
completed value:

```rust
pub enum HeapConstructionState {
    Allocated,
    Initializing { initialized_fields: Vec<ItemId> },
    FullyInitialized,
}
```

Field initialization records completion in source order. The reference cannot
publish to ordinary source storage until all required fields are initialized.
A trap destroys only the recorded initialized fields and does not run the
partial object's direct hook; hooks of completed inline field values still run
before their after-hook structural cleanup.

Internalize and Externalize are atomic MIR ownership operations whose lowering
must preserve a read-only preflight and infallible commit. Their failure edge
leaves source operands, field state, region membership, and root counts
unchanged. An ordinary `Place` may describe a source heap field for diagnostics
and loans, but lowering must not turn it into a generic Talk IR address.

### MIR verifier additions

The ownership verifier must establish:

- every Alias selected by the contextual matrix creates one live external-root
  obligation and does not consume the source;
- every Move from external storage transfers that obligation exactly once, and
  no last-use analysis changes Alias into Move;
- every heap-containing owned value is released, transferred, or consumed by
  heap-field internalization on finite exits;
- Internalize performs complete read-only preflight before one infallible
  commit; failure preserves sources, fields, region membership, and root counts;
- Externalize performs the same complete preflight discipline, acquires every
  inline nested reference and clears the field only in its infallible commit,
  and publishes no partial external value;
- heap-internal after-hook destroy skips those roots while still destroying
  buffers, host handles, and other owned fields and cannot redispatch a direct
  or inline hook visited by the hook prepass;
- construction state prevents publication before full initialization; partial
  objects omit their direct hook, run hooks for completed inline field values,
  and destroy only recorded initialized fields without hook redispatch;
- buffer slot state and source element ownership agree;
- Take deinitializes one slot and Initialize initializes one slot;
- immutable/static buffers are never mutation targets;
- CoW mutation has a verified uniqueness/detachment path;
- pins cover only fully initialized Byte ranges; pin token and address
  lifetimes are balanced and do not cross suspension;
- a mutable pin proves a unique dynamic buffer and conflicts with every retain
  until unpin;
- deinit-self teardown views cannot escape or move, take, destroy, or
  deinitialize their underlying storage;
- heap references do not enter deferred storage, closure, or existential
  boundaries.

MIR still owns source diagnostics and complete provenance. A target runtime
failure is defense in depth, not a replacement for a statically visible error.

## Talk IR impact

### Types

The current `IrType::Address` and `IrTypeDefinitionKind::HeapObject` are not
sufficient by themselves. Proposed distinctions:

```rust
pub enum IrType {
    // existing scalar, aggregate, function, continuation cases...
    ManagedBuffer(IrTypeId),
    HeapBuilder(IrTypeId),
    HeapReference(IrTypeId),
    HeapTransitionPlan,
    Reference(Box<IrType>),
    Address(Box<IrType>),
    PinnedByteRange,
    PinToken,
    HostHandle(IrHostResourceId),
}

pub enum IrTypeDefinitionKind {
    Struct { fields: Vec<IrField> },
    Enum { variants: Vec<IrVariant> },
    ManagedBuffer { element: IrType },
    HeapObject { fields: Vec<IrField> },
    Opaque,
}
```

`ManagedBuffer(IrTypeId)` names a `ManagedBuffer` definition whose element type
is monomorphic. `HeapBuilder(IrTypeId)` is the unpublished allocation/init
capability; only successful completion yields `HeapReference(IrTypeId)`.
`HeapTransitionPlan` is a non-storable affine result of successful read-only
preflight and can only be consumed by its matching infallible commit.
`Reference` is a verified non-owning internal reference and `Address` is a
scoped storage address. `PinnedByteRange` cannot represent an arbitrary Element
payload. A later G0 review may encode these with fewer Rust enum variants, but
the verifier must still distinguish their semantic classes.

`Character` should stop being a scalar `IrType` when R1 is admitted. It lowers
to the borrowed view aggregate adopted by ADR 0033. Until then, every backend
continues to reject Character.

### Generated function identity

Add semantic function roles:

```rust
pub enum IrFunctionRole {
    Source,
    Glue(IrGlueIdentity),
}

pub struct IrGlueIdentity {
    kind: IrGlueKind,
    ty: IrType,
    selected_callees: Vec<IrFunctionId>,
}

pub enum IrGlueKind {
    Clone,
    RunHooks(IrDestroyMode),
    DestroyAfterHooks(IrDestroyMode),
    Destroy(IrDestroyMode),
    BufferDetach,
    HeapRunHooks,
    HeapDestroyFieldsAfterHooks,
    HeapInternalize,
    HeapExternalize,
}

pub enum IrDestroyMode {
    ExternalOwned,
    HeapInternal,
}
```

`selected_callees` in this sketch denotes exact materialized clone/Deinit
implementations, not a witness table or a search input. Ordinary Destroy keeps
its existing per-value ordering: direct hook, then each reverse-order field's
ordinary hook and structural teardown. RunHooks plus DestroyAfterHooks is a
separate split reserved for two-phase heap-region teardown.
`DestroyAfterHooks(ExternalOwned)` releases nested heap roots;
`DestroyAfterHooks(HeapInternal)` skips those roots but still destroys buffers,
host handles, and other owned fields. Heap phase two can call only after-hook
glue, which cannot redispatch direct or inline hooks visited by RunHooks.
The final shape may use stable generated identities before dense `IrFunctionId`
translation. It must remain verifiable and printable.

### Managed instructions

The target-neutral operation set needs semantic operations equivalent to:

```rust
pub enum ManagedInstructionKind {
    BufferAllocate { buffer: IrTypeId, capacity: ValueId },
    BufferCapacity { buffer: ValueId },
    BufferReadCopy { buffer: ValueId, index: ValueId },
    BufferBorrow {
        buffer: ValueId,
        index: ValueId,
        permission: BorrowPermission,
    },
    BufferTake { buffer: ValueId, index: ValueId },
    BufferInitialize { buffer: ValueId, index: ValueId, value: ValueId },
    BufferSwap { buffer: ValueId, lhs: ValueId, rhs: ValueId },
    BufferIsUnique { buffer: ValueId },
    BufferRetain { buffer: ValueId },
    BufferBeginRelease { buffer: ValueId },
    BufferDeallocate { buffer: ValueId },
    BufferCopyBytes { /* source/destination ranges */ },
    ByteBufferPin { /* initialized Byte range/permission */ },
    ByteBufferUnpin { token: ValueId },

    HeapAllocate {
        ty: IrTypeId,
        run_hooks: IrFunctionId,
        destroy_fields_after_hooks: IrFunctionId,
    },
    HeapReadCopy { object: ValueId, field: u32 },
    HeapAcquireAliasField { object: ValueId, field: u32 },
    HeapBorrowField { object: ValueId, field: u32, permission: BorrowPermission },
    HeapInitializeField { builder: ValueId, field: u32, value: ValueId },
    HeapFinishInitialization { builder: ValueId },
    HeapPreflightInternalize {
        target: ValueId,
        field: u32,
        value: ValueId,
        glue: IrFunctionId,
    },
    HeapCommitInternalize { plan: ValueId },
    HeapPreflightExternalize {
        object: ValueId,
        field: u32,
        glue: IrFunctionId,
    },
    HeapCommitExternalize { plan: ValueId },
    HeapMerge { target: ValueId, reference: ValueId },
    HeapRootAcquire { reference: ValueId },
    HeapRootRelease { reference: ValueId },
}
```

These names are illustrative. Required semantic distinctions are normative:

- `BufferBeginRelease` consumes one owner and returns whether final-owner glue
  must run while the payload remains live.
- `BufferDeallocate` is legal only after a final-owner result and complete slot
  destruction.
- allocation returns only `HeapBuilder`; field initialization records completed
  fields, and `HeapFinishInitialization` publishes the ordinary reference only
  after every required field is initialized.
- heap root release and heap allocation can synchronously invoke generated
  recursive-hook and after-hook field-destruction code. They must therefore be
  represented as ordered call-like operations if the IR's instruction model
  cannot safely hide calls.
- `HeapAcquireAliasField` preflights the internal handle and count arithmetic,
  then infallibly acquires one external root without changing the field;
- successful Internalize/Externalize preflight returns one non-storable
  `HeapTransitionPlan` without mutation; its matching commit consumes the plan,
  is infallible, and cannot be separated by arbitrary user code.
- a heap-field take preflights exact externalization glue and its commit acquires
  every nested root before clearing the field; a plain Move is invalid.
- heap field initialization preflights exact internalization glue for nested
  inline heap references; commit merges first and then ends the consumed
  external-root obligation, while finalization does not release that internal
  edge again.
- generic `Load`, `Store`, `Allocate`, and `Deallocate` cannot stand in for
  managed operations.

Pinning may return one small aggregate containing the pinned Byte address and
token rather than adding multi-result SSA. The address and token classes must
remain visible to verification. Mutable pin verification rejects every buffer
retain until the matching unpin.

### Talk IR verifier additions

For each function, verification derives value types from definitions and checks:

- managed type-definition and operation compatibility;
- element, index, capacity, and permission operand types;
- static/immutable mutation rejection; static retain/release are no-ops whose
  ownership balance is nevertheless proven structurally;
- address/reference/pinned-Byte-address nonescape;
- exact generated glue identity, destroy mode, hook/after-hook role, and
  signature;
- separate exact recursive-hook and after-hook field-destruction registration on
  heap allocation;
- HeapBuilder publication only after complete field initialization; partial
  cleanup visits only initialized fields and omits the incomplete object hook;
- internalize/externalize symmetry for every inline nested heap reference;
- transition preflight plans are non-storable, perform no mutation, are consumed
  once by the matching adjacent infallible commit, and cannot cross user code;
- final-owner control paths before buffer deallocation;
- initialized Byte-range pin dominance, use, and single unpin on finite paths;
- no retain while a mutable pin is active;
- heap root acquire/release balance as explicit ownership operations;
- no target runtime symbol, pointer width, object index, or control-block
  offset in semantic IR.

The verifier need not prove dynamic indices in range, but it must require the
checked operation whose runtime semantics include the bounds and initializedness
check.

### Global destruction and trap cleanup

Extend the module with an explicit reverse schedule:

```rust
pub struct TalkIrModule {
    // existing fields...
    global_destructors: Vec<IrGlobalDestructor>,
}

pub struct IrGlobalDestructor {
    global: IrGlobalId,
    guard: IrGlobalGuard,
    destroy: IrFunctionId,
}

pub enum IrGlobalGuard {
    Initialized,
}
```

Every resource-owning global has one canonical runtime initialized bit. The only
accepted destruction action is `Initialized`: test the bit, atomically clear it
before cleanup, call exact external Destroy if it was set, and otherwise no-op.
Early destruction, mutable replacement, trap cleanup, and final teardown all
reuse this operation.

The schedule contains every resource-owning global exactly once and is the exact
reverse of the initializer schedule. Linking remaps it with globals and glue,
then verifies consumer-before-supplier order. The runtime tracks which
initializers completed and, if initialization traps, visits only the completed
initialization prefix in reverse; every visit remains guarded.

Moving an owned resource out of global storage is rejected. Global reads that
produce owned values must borrow, use checked heap Alias, or use a selected
clone. Mutable-global replacement structurally destroys the old external owner
and leaves the current initialized value for the final action.

The entry result is transferred into result-owner storage before this schedule
runs. Success and primary runtime-trap paths both reach the schedule after
active-frame generated cleanup. A managed operation that can dynamically trap
must therefore be call-like or carry an explicit failure successor to verified
cleanup; an implicit backend trap edge is not sufficient for R1.

The first cleanup trap becomes a deterministic `trap during cleanup` result
with an exact balance snapshot. No later user code resumes. Host destroy has
already consumed and closed its handle before a host failure is reported.

Required guarded-schedule fixtures cover successful final teardown, conditional
early destroy followed by a final no-op, initializer trap over a partially
completed schedule, and primary entry trap after active-frame cleanup.

## Bytecode target profile sketch

R1 bytecode support should be a new validated profile extension, not admission
of all quarantined memory/object opcodes. The adapter maps each verified Talk IR
operation to one audited target operation or runtime support call.

The validated module must carry enough metadata to check:

- managed and heap type IDs;
- element size/layout selected by target configuration;
- glue function IDs, Destroy modes, recursive-hook/after-hook identities, and
  signatures;
- heap construction state plus transition-preflight plan/commit pairing;
- guarded global destruction actions and managed-operation failure cleanup
  targets;
- operation operand registers and result kinds;
- field and slot indices;
- pin-token use;
- host resource classes when K1 lands.

Compiler-produced bytecode cannot execute through the raw legacy module API.
The successful output remains a proof wrapper that privately owns the raw
module.

The existing `talk-runtime::memory` and `talk-runtime::objects` modules remain
quarantined during G0. A reuse audit must compare them against ADR 0033,
including duplicate-release behavior, finalizing writes, exact glue identity,
and complete resource counters. Passing their current direct unit tests is not
enough.

## Resource report sketch

Extend counted execution conceptually as follows:

```rust
pub struct RunBalance {
    pub live_buffer_allocations: usize,
    pub live_buffer_elements: usize,
    pub live_heap_objects: usize,
    pub live_heap_regions: usize,
    pub finalizing_heap_regions: usize,
    pub live_pins: usize,
    pub live_host_handles: usize,

    pub result_buffer_allocations: usize,
    pub result_buffer_elements: usize,
    pub result_heap_objects: usize,
    pub result_heap_regions: usize,
    pub result_host_handles: usize,
}
```

A backend can expose additional byte counts and diagnostic details. It cannot
omit one of the semantic resource classes it claims to execute. Result
footprint traversal follows verified type/glue metadata, not arbitrary runtime
value guessing. Exactness is a precondition of the R1 profile, not a Boolean
escape hatch: if the backend cannot compute the complete transitive result
footprint, validation rejects that result or the backend leaves R1
unimplemented.

## G0 implementation order after acceptance

1. Amend ADR 0032's use-mode and Talk IR sections with Alias, managed types,
   generated glue roles, region operations, and erasure points.
2. Update `docs/stage-0-contract-types.md` with accepted concrete shapes.
3. Add Rust contract types only; keep production managed forms rejected.
4. Update TypedProgram validation, MIR verification, Talk IR verification, and
   deterministic printers with malformed negative fixtures.
5. Update `docs/backend-status.md` and `docs/backend-parity-ledger.md` to mark
   the contract gate only; G1-G5 remain pending.
6. Audit the old runtime modules against the accepted target boundary before
   reusing any implementation.

No R1 producer, lowerer, runtime, or backend support should land in the Lane D
review stack.
