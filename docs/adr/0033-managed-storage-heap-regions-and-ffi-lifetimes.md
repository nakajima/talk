# 0033 - Managed storage, heap regions, and FFI lifetimes

Status: accepted at P7 as the R1 design contract; implementation requires the coordinated G0 contract stack (2026-07-15)

## Context

ADR 0008 defines the source direction for managed storage and FFI, ADR 0012
defines `Character` as a borrowed grapheme view, and ADR 0032 defines the
canonical compiler pipeline and ownership split. They do not yet define enough
executable semantics for R1.

The missing decisions are observable:

- whether `String`, `Storage`, and `Array` own or borrow their buffers;
- how a buffer produces a concrete `Byte` without exposing a raw pointer;
- when a copy-on-write clone retains a buffer and when it clones elements;
- which generated function runs a user `Deinit` hook and destroys fields;
- what `NominalRepresentation::Heap` means for aliases, cycles, and teardown;
- whether a raw pointer lent to FFI prevents relocation and deallocation;
- how host resources participate in balance accounting;
- which operations are target-neutral Talk IR and which details belong to a
  target runtime.

The reset deliberately quarantined the old byte-memory reference counts, object
arena, region union-find, and finalizer pump. Their behavior is baseline
evidence, not authority. In particular, R1 must not expose the old runtime's
pointer width, object indices, allocation records, or bytecode operations in
Talk IR.

The required baseline includes:

- strings and arrays with deterministic cleanup;
- type-specific `CheapClone` and copy-on-write mutation;
- element finalization, including nested arrays;
- freely aliasing `'heap` references and visible mutation through aliases;
- direct cyclic `'heap` object graphs that tear down without leaks;
- reverse-allocation heap finalization, one user hook per object, and field
  cleanup;
- rejection of heap references in escaping closures, existentials, and raw
  storage containers;
- a deterministic trap on resurrection during heap teardown.

ADR 0029 remains rejected. R1 must not turn every value into a reference-counted
box in order to recover those rows.

## Decision

R1 uses three distinct resource representations:

1. **Managed buffers** use type-specific reference-counted control blocks for
   `String`, `Storage<Element>`, `Array<Element>`, and later `Dict` storage.
2. **`'heap` objects** use merge-only ownership regions with explicit external
   roots. Direct object-field cycles are internal to a region and do not keep
   it alive.
3. **Host resources** use opaque affine handles with an explicit close or
   destroy contract. They are not managed buffers or heap objects.

These policies are represented by target-neutral operations and generated glue.
They do not share one universal retain/release rule.

### V1 allocation effect

`'alloc` remains an inferred core effect. In v1 it is supplied by the runtime's
implicit core handler and is not user-handleable. Lexical allocation handlers,
custom arenas, and region polymorphism remain future source-language work.

This narrows ADR 0008's handler examples for v1 without removing allocation
from function contracts. A future custom allocation handler must preserve the
managed operation semantics below or introduce a new accepted contract.

## Managed buffers

### Abstract representation

A managed buffer is a target-neutral handle to one control block and one
contiguous element payload. Its semantics include:

- a monomorphic element type;
- capacity;
- per-slot initialized state;
- owner count for copy-on-write sharing;
- immutable/static versus mutable/dynamic storage;
- active immutable and mutable pin state;
- live/finalizing/dead state.

The concrete header, pointer width, alignment, allocation strategy, initialized
bitmap representation, and atomicity are target details. V1 execution is
single-threaded, so owner-count operations need not be atomic. A later
concurrency decision must revisit that point.

Zero-capacity buffers are valid and still have a distinct live handle. Bounds,
initializedness, duplicate release of a dynamic owner, use-after-release, and
pin violations fail deterministically. A backend may remove a check only when
it proves the same condition from verified Talk IR.

Static buffers, including UTF-8 string literals and generated Unicode tables,
implement the same read interface. They are immutable, never unique, need no
owner-count changes, and are not reported as live dynamic allocations. Static
retain and release are runtime no-ops. Because static storage has no per-owner
runtime state, duplicate static ownership transitions are rejected by MIR and
Talk IR verification rather than detected dynamically; v1 does not add
per-owner runtime tokens solely for static data.

### Ownership and views

`Storage<Element>` owns one buffer handle. `Array<Element>` owns a storage
handle, an initialized element count, and a capacity consistent with the
buffer. An owned `String` owns an immutable `Byte` buffer and a byte count; its
owned range starts at zero.

`Substring`, `UTF8View`, and `Character` are borrowed views. Their executable
shape is:

```text
borrowed buffer reference + byte start + byte count
```

A view does not retain the buffer and has no destroy glue. Its source loan keeps
the owner live. MIR verifies the complete loan and escape restrictions before
Talk IR erases the source loan to an internal reference. Mutation or growth of
the owner conflicts with a live shared view, so the viewed payload cannot move
or disappear during the view's extent.

`Character` is therefore not an integer code point, a runtime scalar, or an
owned mini-string. `Character.to_string()` is the explicit allocation and copy
boundary.

### Concrete Byte production

A concrete `Byte` is produced only by a checked read of an initialized slot in
a `Byte` buffer, or by a canonical Byte constant. The operation returns an
ordinary Copy scalar. Byte-to-Int then uses the scalar intrinsic adopted by ADR
0032.

Neither TypedProgram, MIR, nor Talk IR exposes a `RawPtr` to implement a safe
byte read. A backend cannot reinterpret `Character` or `String` as a scalar to
avoid the buffer operation.

### Buffer operation semantics

The target-neutral managed operation vocabulary distinguishes at least:

- allocate a buffer of a monomorphic element type and capacity;
- query capacity;
- Copy-read or borrow an initialized slot;
- move/take an initialized slot, leaving it uninitialized;
- initialize an uninitialized slot;
- swap initialized slots;
- test uniqueness;
- retain one buffer owner;
- begin release of one buffer owner and report whether final-owner teardown is
  required;
- deallocate a finalizing buffer after every initialized element is destroyed;
- copy initialized Byte ranges;
- pin and unpin a fully initialized Byte range for safe FFI.

A generic untyped load, store, or pointer-add operation is not an alternative
safe representation. Unsafe raw-memory operations remain behind the later
K1/unsafe contract.

`begin release` consumes exactly one owner. If another owner remains, no element
is destroyed. If it reports the final owner, the payload stays accessible only
to the generated destroy glue until that glue destroys every initialized
slot and deallocates the control block.

## Clone, destroy, Deinit, and copy-on-write order

### Generated glue

The lowerer emits one monomorphic generated function for every demanded glue
identity. At minimum the identity distinguishes:

```text
Clone(type, selected witnesses)
RunHooks(type, ExternalOwned, selected witnesses)
RunHooks(type, HeapInternal, selected witnesses)
DestroyAfterHooks(type, ExternalOwned, selected witnesses)
DestroyAfterHooks(type, HeapInternal, selected witnesses)
Destroy(type, ExternalOwned, selected witnesses)
Destroy(type, HeapInternal, selected witnesses)
BufferDetach(type, selected witnesses)
HeapRunHooks(heap type, selected witnesses)
HeapDestroyFieldsAfterHooks(heap type, selected witnesses)
HeapInternalize(stored type)
HeapExternalize(stored type)
```

Glue identity is semantic metadata on the Talk IR function, not a debug name.
Calls refer to the exact function identity. Talk IR verification checks the
role, storage mode, monomorphic type, signature, selected callees, and call
sites. A backend executes the body and may not reconstruct ownership from a
type layout.

Ordinary `Destroy(mode)` preserves ordinary value semantics: invoke the
nominal's direct hook, then destroy initialized fields in reverse order, with
each nested field's ordinary Destroy running its own hook immediately before
its structural teardown. It is not implemented as a region-wide hooks-first
prepass.

`RunHooks(mode)` and `DestroyAfterHooks(mode)` are the exact split used only
where a two-phase owner, currently a heap region, requires all region-visible
hooks before structural destruction. `RunHooks` recursively invokes selected
hooks of fully initialized inline value instances. MIR verification guarantees
those hooks cannot deinitialize their teardown views, so the prepass itself
leaves storage initialized.
`DestroyAfterHooks(ExternalOwned)` releases heap roots recursively as well as
destroying buffers, host handles, and other owned fields.
`DestroyAfterHooks(HeapInternal)` skips heap-root release because
internalization already ended those external-root obligations, but still
destroys buffers, host handles, and every other owned field. It cannot
redispatch a direct or inline hook visited by `RunHooks`. It may trigger a hook
in a separately managed child graph, such as an element hook reached only when
a buffer release becomes final; that hook was not part of the region prepass
and cannot contain a region-internal heap reference under the v1 boundary. The
storage modes, ordinary Destroy, and hook/after-hook roles are not
interchangeable.

### Ordinary values

Cleanup still follows ADR 0032: values are destroyed in reverse completed-
initialization order. For a nominal value with a user `Deinit` conformance:

1. ordinary generated Destroy glue invokes the selected user hook exactly once;
2. the hook's `self` and aliases derived from it are teardown views of that same
   instance and do not redispatch the hook;
3. after the hook returns, ordinary Destroy processes each still-initialized
   field in reverse completed-initialization order, including that field's own
   hook and structural teardown;
4. the glue then deallocates owned storage, if any.

The hook may read fields and may create unrelated values. It may not move,
take, destroy, or otherwise deinitialize storage through its teardown view, and
that view may not escape. The generated caller remains the sole structural
teardown owner. Cleanup may not expose an unhandled user effect under ADR 0032.
A newly created sibling value is a distinct instance and receives its own hook.

### Copy-on-write

An O(1) `CheapClone` of a buffer-backed value retains the buffer once and
constructs a second owner. It does not retain or clone each element because the
single shared buffer remains the sole owner of those element instances.

Before mutation:

- a unique dynamic buffer may mutate in place;
- a static or shared buffer detaches into a fresh dynamic buffer;
- detachment clones initialized elements in increasing index order using the
  exact selected element glue;
- a partially built destination is destroyed in reverse initialized order if
  construction cannot complete;
- only after all element clones succeed does the owner replace its old buffer
  handle and release that old handle.

A growing unique buffer allocates the new buffer before moving elements. It then
moves initialized elements in increasing index order, marks the old slots
uninitialized, commits the new handle, and deallocates the empty old shell.

Element replacement preserves the language assignment order:

1. evaluate the replacement value;
2. detach the buffer if required;
3. take the old initialized element, leaving the slot uninitialized;
4. destroy the old element;
5. initialize the slot with the replacement.

Array destruction begins release of its buffer. Only the final owner destroys
initialized elements, in reverse index order, and deallocates the buffer.

`Array<Element>` may be selected for `CheapClone` only when every possible
detachment can clone `Element` under already selected Copy or CheapClone
evidence. The current unconditional core conformance is not authority and must
be constrained during the R1 source-core migration. Affine host handles and
other non-cloneable resources may be stored in a unique array, but such an
array cannot be cloned.

## Aggregate fields and projection addresses

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

Heap-object fields do not use ordinary aggregate addresses. Reads, borrows,
takes, initialization, and replacement use heap operations so region merging,
externalization, finalization state, and resurrection checks cannot be
bypassed.

## `'heap` object semantics

### Alias edges

`NominalRepresentation::Heap` means identity and shared reference semantics.
A source use may duplicate a heap reference without invoking the user `Copy` or
`CheapClone` protocols. Type checking must publish a distinct checked `Alias`
edge with structural alias evidence. MIR preserves that edge and verifies the
evidence. Lowering turns it into explicit external-root acquisition.

This is a contract gap in the current ADR 0032 mode vocabulary. R1
implementation cannot begin until the G0 amendment adds Alias to TypedProgram,
CheckedMir, validation, verification, printers, and negative tests. Heap types
remain forbidden from declaring `Copy` or `CheapClone`; intrinsic reference
aliasing is not a value-copy conformance and does not add a `.clone()` witness.

Type checking selects Alias, Move, or Borrow contextually and never from
last-use liveness:

- a borrow parameter, borrowed receiver, or explicit borrow context selects
  `BorrowShared` or `BorrowMut` and adds no root;
- an explicit `consume`, a parameter whose selected passing mode is Consume, an
  owned return edge, or another explicit ownership-transfer context selects
  Move and makes the source unavailable on that path;
- an ordinary owning place use of a heap reference selects Alias, including a
  local binding, assignment RHS, value-aggregate field, or heap-field
  initialization that does not explicitly consume its source;
- a fresh heap rvalue already owns one root and moves that root into its owning
  destination rather than aliasing itself;
- the same rules apply recursively to a value aggregate containing heap
  references: an ordinary duplicate requires structural Alias evidence, while
  a consuming argument, owned return, or explicit transfer moves the aggregate.

Constructor and assignment production must preserve that selected edge for
each source operand. A heap-field destination then internalizes its owned Alias
or Move operand; it never stores a source borrow directly. A backend may not
turn a last use into Move or omit an Alias acquire.

Move between already-external storage transfers an existing root and produces
no acquire. Returning an owned heap reference is such a transfer. Moving from
heap-internal storage is not an ordinary Move: it must first externalize the
stored value as defined below. Copying a value aggregate that contains heap
references requires structural Alias evidence and acquires each represented
external root exactly once.

Structural Alias is limited to lifecycle-trivial value products. Anonymous
tuples and closed records qualify when every component has exact Copy or Alias
evidence. A nominal value struct additionally qualifies only when it has no
user `Deinit` hook, no custom clone/destroy lifecycle, no hidden storage, and
its complete canonical field list is proven component-by-component. Its destroy
behavior is then only the structural cleanup justified by that evidence. A
nominal with its own hook cannot use structural Alias: duplicating it requires
an independently selected Copy or clone authority, or the value must Move. This
prevents one unapproved source use from creating two nominal instances and two
hook invocations.

### Merge-only ownership regions

Every heap allocation starts one fresh ownership region and one external root.
External roots are heap references owned by stack storage, globals, value
aggregates, parameters or results with owned transfer, and other admitted
non-object storage.

Storing a heap reference into a heap-object field makes it internal:

- the target and referenced regions merge;
- the store consumes one owned reference operand; an lvalue source first uses a
  checked Alias edge, while an rvalue may move its existing root;
- `HeapInternalize` releases that consumed external-root obligation after the
  merge, so the internal field edge adds no external root;
- a borrowed reference cannot be stored directly as an owning heap field;
- overwriting or removing the edge does not split the merged region;
- all other external-root counts and object members are preserved by the merge.

Inline tuples, records, structs, and enum payloads stored in a heap field are
walked by exact generated `HeapInternalize` glue so nested heap references merge
as internal edges and their consumed external-root obligations end exactly
once. Heap finalization does not release those internal references again.
Display names and backend scans are not substitutes for that glue.

Internalization is transactional and has a read-only preflight followed by an
infallible commit:

1. recursively enumerate every nested heap reference and consumed root;
2. validate all object handles, source root obligations, region states,
   repeated-reference multiplicities, count arithmetic, destination field
   state, and the complete merge plan without changing region membership, field
   state, source state, or any root count;
3. only if every check succeeds, commit all region merges and end all consumed
   roots; no commit step can fail.

A failed preflight preserves the destination field, every source operand,
region membership, and all root counts exactly. Because merged regions cannot
split, an implementation that mutates during preflight cannot satisfy this
contract.

Taking a heap field into external owned storage performs the inverse transition.
Exact generated `HeapExternalize(stored type)` glue also uses read-only preflight
and infallible commit:

1. recursively enumerate every internal heap reference that will become an
   external owner;
2. validate all handles, region states, repeated-reference multiplicities,
   count arithmetic, destination storage, and the complete field take without
   changing a root count, source state, or field state;
3. only after success, acquire every required external root and clear the field
   as one infallible commit before publishing the external value.

Buffers, host handles, and other uniquely owned components transfer without
duplication. Failed preflight leaves the field initialized and preserves region
membership and root counts exactly; no partial external value is published.
After commit, ordinary external Destroy glue owns the acquired roots. A direct
Move from internal storage is invalid without this transition.

Destroying or replacing a value that remains in a heap field uses
`Destroy(type, HeapInternal)`: it skips internal heap references while still
destroying buffers, host handles, and other owned components. Using ordinary
external Destroy glue there would double-release roots ended by
internalization and is a verifier error.

A region begins teardown when its external-root count reaches zero. Direct
cycles inside the region therefore do not keep it alive. This is not a tracing
or trial-deletion cycle collector: regions only merge and can retain objects
longer than graph reachability strictly requires while any external root into
the merged region remains.

This policy is adopted because it preserves required direct heap cycles,
identity, deterministic teardown, and source aliasing without applying
reference counting to every value. The old runtime implementation may be reused
only after a separate adapter audit proves that it implements this contract
behind the new Talk IR operations.

### V1 cycle boundary

V1 supports heap references nested in inline value aggregates stored directly
in heap fields. It preserves the baseline rejections for paths that hide heap
references behind another independently managed graph:

- escaping closure environments that capture heap references;
- existential payloads containing heap references;
- managed buffers whose element type contains a heap reference when that
  buffer would be stored into a heap region;
- opaque or unsafe raw storage containing heap references.

Arrays of heap references and the relaxation of these field restrictions need a
later design that explains root/internal-edge conversion through shared
buffers. Closure/cell cycles, existential cycles, weak references, and a general
cycle collector are not part of v1.

### Region teardown and resurrection

Every heap record has an explicit construction state:

```text
Allocated       record exists; no field is initialized and it is unpublished
Initializing    a recorded subset of fields is initialized
FullyInitialized all required fields are initialized and the reference may publish
FinalizingHooks hook phase is active; prior completion and field set are retained
FinalizingFields field phase is active; prior completion and field set are retained
Dead            storage is inaccessible
```

Each successful field initialization records its completion before another
field begins. Construction publishes the reference only when the record becomes
`FullyInitialized`. If construction traps, the object itself receives no direct
heap hook, but each already initialized field remains an ordinary completed
value whose nested hooks and structural cleanup must run. Uninitialized fields
are never read, hooked, or destroyed.

When the final external root is released, teardown has two separate phases:

1. mark every record in the complete merged region as `FinalizingHooks` before
   running user code;
2. visit records in reverse successful allocation order with exact
   `HeapRunHooks` glue:
   - for a record that entered teardown fully initialized, invoke its selected
     direct heap hook;
   - for both fully and partially initialized records, recursively run
     `RunHooks(HeapInternal)` for each initialized inline value field in reverse
     completed-initialization order;
   - throughout this phase every initialized object field remains initialized
     and readable, including fields reached through a cycle;
3. after all region-visible hooks return, mark every record
   `FinalizingFields`, then visit records in the same reverse allocation order
   with exact `HeapDestroyFieldsAfterHooks` glue; destroy only initialized
   fields, in reverse completed-initialization order, using
   `DestroyAfterHooks(HeapInternal)`;
4. after all structural field destruction completes, mark records `Dead` and
   bulk-deallocate the region.

No region-visible hook runs after field destruction begins. The readable-field
promise applies to the hook phase, not to arbitrary code after the field phase
starts. Phase-two glue is verifier-proven incapable of dispatching a direct or
inline hook that phase one already ran.

Managed buffers remain an independently owned graph. If a heap field's buffer
release is not final, its elements survive and receive no hooks. If it is final,
element hooks may run during buffer destruction, but the existing v1 boundary
forbids such a buffer's element type from containing a heap reference when the
buffer is stored in a heap region. Those element hooks therefore cannot observe
region-internal objects through their element value. Relaxing that restriction
requires bringing those buffers into the region hook prepass.

A deinit-created independent object starts a fresh region and may tear down
nested inside the current hook when its own last root is destroyed.

Resurrection is forbidden. A reference into a finalizing region cannot become a
new external root, escape from a hook, or be stored into another region. Heap
field writes are forbidden while their region is finalizing. Statically visible
escapes are MIR ownership errors; dynamic attempts trap deterministically.
Deinit-local aliases of the current object are teardown views, not roots.

Duplicate root release, access to a dead object, or a store involving a
finalizing region is a deterministic runtime error. It is never silently
ignored.

## FFI pinning and host resources

### Scoped buffer pinning

Safe v1 FFI obtains an address only through a scoped pin over a fully
initialized range of a managed `Byte` buffer. Arbitrary `Element` buffers are
not safely pinnable: their payload may contain uninitialized slots, padding,
heap references, host handles, or a target-specific representation. Widening
safe pinning requires a later accepted FFI-safe representation class.

Pinning validates the complete Byte range, then returns a non-storable
pinned-address capability and an affine pin token. The token carries a pin
lease, not a copy-on-write owner, and must be consumed by unpin on every finite
path.

During the pin:

- the control block and payload address remain live and stable;
- immutable pins may coexist, and ordinary buffer retain may create another
  CoW owner while immutable pins are active;
- a mutable pin requires a unique dynamic buffer and exclusive source loan;
- buffer retain is forbidden while a mutable pin is active, so the unique
  buffer cannot become shared through a clone;
- detach, growth, final-owner release, deallocation, and conflicting mutation
  are forbidden; a non-final owner release during immutable pins is permitted;
- the address and token cannot be returned, stored, captured, serialized, or
  carried across user-effect suspension.

A pin does not change the buffer owner count. Runtime pin state prevents final
release or relocation even if malformed target code attempts it; MIR and Talk
IR verification still require unpin before the source owner can die. Static
Byte ranges may be pinned immutably and never mutably.

This follows the ordinary pinning guarantee: a pointee remains valid at one
address for the pin's lifetime. The address may become invalid immediately
after unpin. `withUnsafeBytes` and `withCString` express this with a nonescaping
callback; they do not return a pointer. `withCString` first provides a fully
initialized, NUL-terminated Byte range; the pin operation does not invent a
terminator.

Heap object layout is not pinnable or FFI-visible in v1. A heap object may be
passed only as an opaque host token through an explicit adapter.

### Host handles

A host resource is an opaque target-neutral handle class supplied by a stable
host import contract. Creation returns one owned affine handle. Move transfers
it. Duplication is available only when the host contract publishes an explicit
clone operation. There is no implicit host-handle reference count.

Generated destruction uses one exact non-discontinuing core operation with the
signature `(OwnedHostHandle) -> Unit`. It exposes no user effect. The operation
atomically consumes and marks the handle closed before invoking the host
adapter. A host failure is a deterministic runtime error and the handle remains
closed; cleanup never retries it or restores an owned handle. The host adapter
must remove the handle from the live-resource ledger even on that failure.

An explicit source `close` is separate. It may expose IO and return a checked
failure value, but it consumes the handle, so later generated cleanup has no
handle to destroy.

Borrowed host handles never close the resource. Owned and borrowed policies are
part of the import signature and cannot be selected by a backend-local name
switch. Host callbacks cannot retain a lent buffer pointer or borrowed handle
unless a separate source-visible ownership transfer operation says so.

Strict-linear host handles in heap objects, CoW buffers, closures, and
existentials remain deferred. R1 first admits affine handles whose deterministic
destroy path is representable by generated glue.

## Global destruction schedule

Every linked executable with resource-owning globals has one explicit global
destruction schedule derived from its verified initialization schedule. It is
part of Talk IR, not a backend convention.

- Each successfully initialized global is recorded exactly once and owns one
  canonical runtime initialized bit.
- Every early or final destruction action is
  `DestroyGlobalIfInitialized(global, destroy)`: it tests the bit, atomically
  clears it before entering user or host cleanup, calls exact external Destroy
  only when the bit was set, and otherwise performs a verified no-op.
- Destruction visits only completed initializations, in the exact reverse of
  their completed initialization order.
- Because linking initializes suppliers before consumers, reverse destruction
  destroys consumers before suppliers. Within a module it reverses the
  producer-published source declaration order.
- Each action calls exact external Destroy glue for the global type. That glue
  releases managed buffers and heap roots and destroys host handles once.
- Literal/static globals with no owned dynamic resource have a verified no-op
  action rather than an inferred backend exemption.

R1 does not permit moving an owned resource out of global storage. A result or
local derived from a global must borrow, use checked heap Alias, or use a
selected clone. Mutable-global replacement evaluates its RHS, invokes the same
guarded destroy action for the old value, stores the replacement, and sets the
initialized bit. An explicit early destroy uses the guard and leaves the global
uninitialized until a later explicit initialization permitted by its
mutability contract. The final schedule reuses the guard, so conditional or
repeated schedule reachability cannot double-destroy the slot.

After the selected entry returns, its owned result is first materialized in the
harness's result-owner storage. This is a real ownership transfer: any heap root,
buffer owner, or host handle in the result is independent of the globals. The
runtime then executes the global destruction schedule before returning the
result to the embedding caller or measuring its transitive result footprint.
Destroying the result afterward must reduce the remaining live footprint to
zero.

A runtime trap follows an explicit failure-cleanup path. The target first runs
generated cleanup for initialized values in active frames, then visits every
completed global in the same reverse guarded schedule, and only then reports
the primary trap and balance snapshot. If an initializer traps before its
result is stored, that global's bit remains clear and only earlier completed
globals destroy. Invalid bytecode rejected before execution has initialized no
globals and runs no schedule.

A second trap while generated cleanup or global destruction is already running
terminates teardown with a deterministic `trap during cleanup` error and a
balance-at-trap report; no backend may silently continue user code or invent a
different destroy order. Host destruction still marks its handle closed before
reporting host failure, as specified above.

Talk IR operations that can dynamically trap while managed resources are live
must expose an explicit failure successor or equivalent verified cleanup edge.
A target-local trap that bypasses those edges cannot claim the R1 profile.

## Target-neutral Talk IR boundary

Talk IR owns semantic operation identity and ordering. It must represent:

- managed-buffer and heap-reference types distinct from raw addresses;
- buffer slot initializedness operations;
- explicit buffer retain, final-owner release, and deallocation;
- explicit heap root acquire/release, region merge, and transactional
  internalization/externalization preflight and commit;
- unpublished heap construction state, initialized-field state, and publication
  only after full initialization;
- heap allocation with separate exact recursive-hook and after-hook
  field-destruction identities;
- external-owned versus heap-internal and hook versus after-hook Destroy roles;
- scoped Byte-range pin and unpin;
- generated glue roles and exact calls;
- opaque host handle types and stable host imports;
- the initialized-bit-guarded global destruction schedule and
  managed-operation failure-cleanup edges.

Target adapters own:

- control-block and object-header layout;
- pointer width, alignment, and ABI;
- buffer owner-count storage;
- region union-find or an observationally equivalent implementation;
- finalizer dispatch tables and calling convention;
- pin representation;
- host API handles and platform error conversion.

A backend may choose a different data structure from the old runtime, but it
must preserve the operation semantics, ordering, traps, and resource counts. It
may not scan source types to discover fields, infer cleanup from liveness, or
map a display name to a runtime function.

The accompanying proposed Rust-shaped changes are in
[`docs/r1-managed-storage-contract-sketch.md`](../r1-managed-storage-contract-sketch.md).
They are not production contracts until this ADR is accepted and the G0 stack
updates ADR 0032, Stage 0, Rust types, validators, verifiers, and printers.

## Cross-artifact laws

### Representation law

`NominalRepresentation::Value` remains a value aggregate even when one of its
fields is a heap reference. `NominalRepresentation::Heap` lowers to exactly one
heap-object type and heap-reference representation. Representation does not
become contagious through fields.

### Alias and root law

Every source heap duplication has one checked Alias edge selected by context,
never by liveness. Structural Alias evidence for a nominal also proves that its
own lifecycle is trivial. Every verified Alias edge produces exactly one
external-root acquire per represented heap reference. Move between external
owners produces none and borrow produces none. A heap-field internalization
consumes its owned operand by merging and ending that root. A take from internal
storage first externalizes and acquires each nested root before clearing the
field. External Destroy releases those roots; internal Destroy does not. No
target adapter invents alias, internalization, or externalization edges.

### Root-transition transaction law

Internalize and Externalize perform complete read-only preflight before any
region, root-count, field-state, or source-state mutation. A failed preflight
leaves all four unchanged. After success, commit is infallible and publishes no
intermediate state.

### View erasure law

Every `Substring`, `UTF8View`, and `Character` reference in Talk IR derives from
a verified MIR loan. Erasure adds no retain and no escape. The same source range
and byte range reach buffer operations.

### Buffer initialization law

MIR ownership of elements and Talk IR buffer slot state agree: initialize targets
an uninitialized slot, read/take targets an initialized slot, take
uninitializes it, and final-owner destruction visits each remaining initialized
slot exactly once.

### Glue identity law

The selected clone and Deinit witnesses, monomorphic type, field order, and
generated glue identity are preserved exactly from CheckedMir through Talk IR.
A glue call cannot be replaced by another function with a compatible display
name or signature.

### Cleanup order law

Source reverse-initialization cleanup order reaches generated glue unchanged.
CoW detachment, replacement, two-phase heap teardown, nested finalization,
global destruction, trap cleanup, and Discontinue paths preserve the ordering
defined above. Direct heap hooks and recursively reachable inline value hooks
complete while region fields remain initialized; only then may after-hook
internal field destruction begin. Partial records run no direct object hook and process
only their initialized fields.

### Region boundary law

Only explicit root operations affect the external-root count. Only explicit
internalization/merge operations create region edges. A backend scan, garbage
collector root guess, or raw pointer store cannot alter the answer.

### Pin and host ownership law

Every safe pin covers a fully initialized Byte range and has one unpin on each
finite path. A mutable pin cannot coexist with a buffer retain. Every owned host
handle has one close, transfer, or accounted result owner. Generated host
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

A generic, existential, closure, buffer, host, or heap combination outside the
v1 boundary rejects before partial lowering. Raw pointers cannot be used as a
fallback representation for safe managed operations.

## Verifier obligations

### TypedProgram validation

- Heap aliases carry exact structural Alias evidence and are selected by the
  contextual rule above without last-use information.
- Nominal structural Alias evidence proves no user Deinit hook, custom
  lifecycle, hidden storage, or omitted field; a lifecycle-bearing nominal
  requires Copy/clone authority or Move.
- Consuming arguments, owned returns, explicit transfers, ordinary owning
  assignments, aggregate fields, and heap-field initializations publish the
  required Move, Alias, or Borrow edge exactly once.
- Heap declarations cannot claim `Copy` or `CheapClone`.
- Selected buffer clones prove every future detachment can clone the element.
- Borrowed views cannot appear in owned fields, globals, or escaping captures.
- Unsafe/FFI ownership policies and nonescaping callback shape are explicit.

### CheckedMir verification

- Alias, external Move, borrow, clone, both Destroy modes, internalization,
  externalization, and root ownership agree on every CFG path.
- Internalize and Externalize preflight every nested reference and transition
  without mutation; failed preflight preserves source, field, regions, and root
  counts, while successful commit is infallible.
- A take from heap-internal storage acquires every nested root before clearing
  the field; internal destruction skips those roots but still destroys other
  resources.
- Heap construction tracks Allocated, Initializing, FullyInitialized, both
  finalizing phases, and Dead; partial cleanup visits only initialized fields
  and omits the incomplete object's direct hook.
- Region hook traversal recursively runs initialized inline value hooks, and
  phase-two DestroyAfterHooks cannot redispatch them.
- Buffer slot initialization and element ownership agree at each operation.
- Replacement and detachment order is structural.
- Every pin covers a fully initialized Byte range, every pin token is unpinned
  on every finite normal, early, trap-cleanup, and discontinue path, and no
  pinned address crosses suspension or escape.
- Mutable pins prove uniqueness and reject retain or sharing while active.
- Deinit teardown views cannot escape or move, take, destroy, or deinitialize
  their storage; heap finalization views obey the same rule and obvious
  resurrection is rejected.
- Deferred heap-containing storage, closure, and existential forms reject.

### Talk IR verification

- Managed operation arity and operand/result types are exact.
- Buffer and heap operations cannot be performed through generic addresses.
- Generated glue roles, storage modes, hook/after-hook behavior, and exact
  signatures are unique per demanded identity.
- Heap allocation registers separate matching monomorphic recursive-hook and
  after-hook field-destruction glue plus explicit construction state.
- Internalize and Externalize glue recursively agree on every inline heap
  reference in the stored type and expose preflight/commit semantics.
- Final-owner buffer paths destroy each initialized element before deallocation.
- Pin tokens dominate Byte-address uses and are consumed once on every finite
  path; mutable pin paths contain no retain.
- Host imports have stable identities and exact ownership/effect signatures.
- The global destruction schedule contains each initialized resource-owning
  global exactly once in reverse initialization order, every action uses and
  clears the canonical initialized bit, and failure edges reach it after
  active-frame cleanup.
- Raw addresses, target-specific runtime names, and unverified layout constants
  do not appear.

### Backend validation

- Encoded operations, indices, types, glue references, and control targets are
  valid before execution.
- Dynamic bounds, initializedness, owner-count, region-state, pin-state, and
  host-handle failures return deterministic errors rather than panicking or
  executing unchecked.
- Root-transition preflight performs no mutation and target commit cannot fail;
  object and global initialized-state guards match verified Talk IR.
- A backend claiming R1 reports the complete and exact resource balance below;
  an inexact result footprint rejects the profile.

## Resource oracles

Every successful R1 G5 fixture reports:

```text
live dynamic buffer allocations
live initialized buffer elements
live heap objects
live heap regions, including finalizing regions
live pins
live owned host handles
result-owned footprint for each category
```

All live counts must equal the exact transitive footprint intentionally owned
by the returned result. A backend that cannot compute that footprint exactly
rejects the result or remains outside the R1 profile; inexact accounting is not
an exemption. After the harness destroys that result, every count is zero.
Static buffers are reported separately and do not count as leaks.

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
- internal aggregate extraction through HeapExternalize;
- internal aggregate replacement and teardown through internal Destroy;
- interior heap alias returned from a merged region;
- heap objects with managed-buffer fields;
- partial heap construction destroying only initialized fields without the
  incomplete object's direct hook;
- two-phase reverse-allocation direct and nested inline hooks followed by
  after-hook field destruction;
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
- host close, transfer, destroy failure after close, duplicate-close rejection,
  and result ownership.

No resource exemption is anonymous. A temporary unsupported case has a parity
ledger row and removal condition.

## Explicitly deferred

- user-handled allocation effects, lexical arenas, and region polymorphism;
- concurrent sharing and atomic buffer owner counts;
- general tracing or trial-deletion cycle collection;
- weak or unowned heap references;
- closure/cell, existential, managed-buffer-mediated, and host-mediated heap
  cycles;
- heap references in raw storage and FFI-visible heap layout;
- strict-linear resources inside heap objects or shared buffers;
- addresses or pins across effect suspension;
- host-retained callbacks and asynchronous FFI pointer loans;
- unsafe arbitrary pointer arithmetic and typed raw-memory loads/stores;
- resurrection.

These are deliberate v1 boundaries, not invitations for backend fallback.

## Alternatives rejected

### Reuse the old runtime contract unchanged

Rejected. It would make object indices, byte-vector addresses, region ledger
quirks, and finalizer-pump control flow compiler contracts. Reuse is permitted
only behind the semantic operations adopted here.

### Uniform reference counting

Rejected again. Buffer CoW counts and heap-region external roots are
purpose-specific. Value aggregates, unique affine values, and host handles do
not acquire a universal count.

### Tracing GC for heap cycles

Rejected for v1. It does not by itself provide deterministic hook timing or
reverse-allocation order, and it is unnecessary for the required direct object
cycles under merge-only regions.

### Raw pointers as Talk IR managed values

Rejected. They lose ownership class, bounds, initializedness, pin state,
backend independence, and safe FFI lifetime information.

### Make borrowed views retain buffers

Rejected. It duplicates source borrow semantics at runtime, changes CoW
uniqueness, and permits a borrow-checker error to become an accidental owned
escape. Verified source loans are the authority.

## Research and precedent

- Gay and Aiken, *Language Support for Regions*, PLDI 2001: region reference
  counting and region lifetime as the basis for merge-only ownership regions.
- Arvidsson et al., *Reference Capabilities for Flexible Memory Management*,
  OOPSLA 2023 / arXiv 2309.02983: explicit capability-controlled memory
  management and deterministic region finalization as the modern comparison
  point for finalise-then-free behavior.
- Rust's `std::pin` contract: a pinned pointee remains valid at one address
  through the pin lifetime and must run destruction before invalidation.
- Swift's scoped `withUnsafeBytes` APIs: unsafe addresses are lent to a
  nonescaping operation instead of becoming ordinary owned values.
- Rust MIR drop elaboration and Swift Ownership SSA, as cited by ADR 0032:
  initializedness and consuming operations are structural IR facts, while
  generated cleanup is verified before target lowering.

## P7 acceptance record

P7 accepted this ADR after review confirmed:

1. the distinct buffer, heap-region, and host-handle policies;
2. the contextual checked Alias edge, lifecycle-trivial structural evidence,
   and ADR 0032 impact;
3. transactional HeapInternalize/HeapExternalize preflight and commit;
4. both Destroy storage modes and hook/after-hook glue identities;
5. the v1 direct-cycle boundary and preserved baseline rejections;
6. partial construction and two-phase recursive-hook/field teardown;
7. guarded global destruction, element order, and trap behavior;
8. the no-resurrection rule;
9. scoped initialized-Byte pinning and non-discontinuing host destruction;
10. the Talk IR operation/glue/failure-edge boundary;
11. exact verifier and resource-oracle completeness.

Acceptance opened only the coordinated G0 contract stack. It did not authorize
runtime, MIR, Talk IR, or backend implementation in the Lane D review worktree.
