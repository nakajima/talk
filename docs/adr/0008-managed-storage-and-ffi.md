# ADR 0008: Managed Storage, Allocation Effects, and FFI

Status: accepted

Date: 2026-06-23

## Context

The current core library exposes `RawPtr` directly:

- `core/Memory.tlk` exports `_alloc`, `_load`, `_store`, `_copy`, and
  pointer arithmetic over `RawPtr`.
- `String` and `Array` store raw pointers as public value fields.
- `IORequest` carries raw pointers for read, write, open, and poll.
- Lowering maps `RawPtr` to lambda-G `Ptr`, and the VM implements this as
  an address into a bump-allocated byte vector.

That is useful for bootstrapping, but it is the wrong safe language
surface. Safe code should not traffic in naked addresses. It should see
owned values, borrowed views, scoped allocation authority, and explicit
unsafe/FFI APIs.

Talk also already has lexical effects. Allocation should use that
machinery instead of being hidden behind an implementation word like
"heap".

## Decision

Safe Talk will move away from public `RawPtr`.

Allocation authority is represented by:

```talk
public enum Allocation {
	case allocate(Int)
	case free
	case retain
	case release
}

public effect 'alloc(allocation: Allocation) -> Void
```

`Allocation` names the operation capability. It does not promise a heap
implementation. A handler may lower allocations to a heap, a region, a
bump arena, stack storage, or native backend allocation primitives.

Raw pointers remain available only behind an unsafe or FFI boundary.
The compiler and backend may still use pointer-shaped IR values
internally.

## Current Implementation Status

The current implementation has landed the first ownership and borrowing
surface pieces:

- core allocation is exposed as
  `'alloc(allocation: Allocation)`, and `_alloc<Element>(count)` lowers
  to element-sized IR allocation;
- `String.slice` returns `Substring`, a borrowed string view;
- source methods use receiver modes instead of explicit receiver
  parameters;
- the parser rejects explicit instance-method `self` parameters;
- type checking rejects assignment through shared borrows, including a
  plain `func` receiver;
- the ownership pass performs move, borrow, loop-carried move, use-before
  initialization, and escaping-borrow checks by executing source-near CFG
  ownership MIR bodies;
- escaping closure values are summarized through locals, returns,
  by-value arguments, aggregate literals, and trailing blocks; closure
  literals support explicit `copy`, `consuming`, `&`, and `&mut` capture
  modes. Borrow captures cannot escape, implicit ownership-sensitive
  captures are rejected, and compiler-managed cells for mutated `Copy`
  locals are allowed because the closure environment owns the cell.

The raw-pointer storage implementation is still temporary. `RawPtr`
remains visible in core storage, arrays, strings, and IO internals, but
safe user sources cannot mention raw pointer types or inline IR unless
the source opts into the unsafe boundary with `// unsafe`.

## Source Model

Safe values fall into these broad categories:

- `Copy`: scalars and aggregates whose fields are all copyable.
- Owned: values that own storage or resources, such as `String`,
  `Array<T>`, `Storage<T>`, closures with owned captures, and protocol
  existentials with owned payloads.
- Borrowed views: `&T`, `&mut T`, `Slice<T>`, and `Substring`.
- Unsafe pointers: `Unsafe.Pointer<T>`, `Unsafe.MutablePointer<T>`,
  `Unsafe.RawPointer`, and `OpaquePointer`.

Owned values move by default. Duplication requires `Copy` or an
explicit `clone`. Dropping an owned value is deterministic.

Borrow lifetimes are initially an internal compiler concept. The
compiler should infer lexical borrow scopes for common cases. Source
level named lifetimes can be added later for APIs that genuinely need
them.

Method receivers are source-level ownership syntax:

- `func get(...)` has a shared receiver and is checked internally as
  borrowed `self`;
- `mut func set(...)` has a mutable receiver and is checked internally
  as mutably borrowed `self`;
- `consuming func into(...)` has an owned receiver and may consume
  `self`.

Source method signatures do not declare `self`. The compiler inserts the
internal receiver parameter after parsing so later passes can type check
and lower methods using ordinary parameter rules.

## Effects And Ownership

Ownership, borrowing, and effects answer different questions:

- Ownership answers who must clean up a value and whether a use moves it.
- Borrow checking answers whether a view can outlive the value it views.
- Effects answer which capabilities the code is allowed to use.

The `'alloc` effect gates allocation, release, retain, and low-level
storage mutation needed to implement safe storage types. It does not
replace move checking or borrow checking.

Compiler-inserted memory drops may lower directly to internal allocation
ops after the ownership pass has proved they are needed and safe.
External resources are different: closing files or sockets performs IO,
so those APIs should remain visibly effectful, usually through scoped
forms such as `withFile` or explicit `close`.

## Managed Storage

The safe library direction is:

```talk
public struct Storage<Element> {
	// compiler-known storage handle
}

public struct Array<Element> {
	let storage: Storage<Element>
	let count: Int
	let capacity: Int
}

public struct String {
	let storage: ByteStorage
	let start: Int
	let length: Int
}

public struct Substring {
	// borrowed byte view
}
```

`String.slice` should return `Substring`, not a second owning `String` that
points into the first string's storage. Copying a slice into owned
storage should be an explicit operation and carry `'alloc`.

IO should use `Slice<Byte>` and `MutableSlice<Byte>` at the safe
surface. Pointer marshalling belongs in lowering or unsafe core code.

## Borrow Checking

The ownership and borrow checker runs after type checking, before
lowering to lambda-G. It consumes the shared source-near Semantic MIR in
`src/mir`, whose statements retain `NodeID`s and resolved `Symbol`s so
facts can still be tied back to `TypeOutput`, member resolution, and
source expressions. MIR bodies carry owner symbols, locals, operands,
rvalues, and `KeyPath` projections so moves, borrows, drops, and later
lowering can refer to source-shaped values such as `self.path` instead of
only local variables.

The Semantic MIR layer is deliberately local: it is built per body,
caches source-order use counts during construction, records explicit
points, scopes, storage live/dead markers, assignment replacement sites,
and drop candidates, then executes move/borrow events with a worklist
over the body's CFG successors. Branches, switches, and loops merge
ownership states at CFG joins, so a move or live loan that can reach a
block along any path is visible when that block is checked. This is a
per-body fixed point, not a whole-program fixed point, which keeps
compile-time cost bounded while giving source semantics a CFG-shaped home
before lambda-G lowering.

It currently checks:

- borrowed types cannot be stored in owned struct fields or globals;
- borrowed values that refer to local storage cannot be returned;
- non-copy owned values move by default;
- use-after-move diagnostics;
- use before initialization is rejected;
- loop-carried moves are visible on later loop iterations;
- borrows become invalid after the owner moves or is reassigned;
- assignment through a shared borrow is rejected;
- implicit ownership-sensitive closure captures are rejected; explicit
  capture lists support `copy`, `consuming`, `&`, and `&mut`, including
  captures that flow through local function values, returned aggregates,
  by-value call arguments, and trailing blocks;
- compiler-managed cells for mutated `Copy` locals may escape in
  closures, but source borrow captures and polymorphic or owned cell
  captures are rejected;
- internal origin/loan/storage/move/assignment/drop facts are recorded;
- `needs_drop(T)` is derived from actual types, with `Borrowed`
  nominals overriding owned fields;
- drop elaboration classifies candidates as static, dead, conditional, or
  open and writes that checked annotation back onto MIR drop candidates.

Assignment writability is also checked during type checking. A plain
method `func` has a shared receiver, so `self.field = value` is rejected
with a diagnostic telling the author to use `mut func` when mutation is
intended.

The remaining borrow work is:

- richer region/lifetime dataflow for more precise nonescaping captures
  and loop-carried loans;
- executable dynamic drop flags for conditional/open drop obligations;
- explicit lifetime syntax only if real APIs need it.

The current soundness boundary is conservative. Safe Talk should not
accept dangling borrows, use-after-move, moves while borrowed, mutable
aliasing through checked borrow types, or drops of storage that was never
initialized. When the checker cannot prove an ownership-sensitive closure
capture, it rejects the program instead of inferring an implicit heap box
or reference count. Borrowed values should not be storable in owned heap
data until the lifetime model is explicit enough to describe that
soundly. Safe sources also reject `RawPtr` and inline IR; raw pointer
tests and low-level examples must opt into `// unsafe`. The evaluator and
VM now track allocation records, reject double-free and use-after-free,
and treat frees of static storage as no-ops. Drop lowering still needs
dynamic flags for conditional/open obligations so it can free more paths
without becoming unsound.

This follows the same broad shape as Rust's MIR borrow checker: check a
desugared CFG representation, derive regions from CFG points, and use
dataflow before reporting move/borrow errors. See the Rust compiler
development guide on [MIR borrow checking](https://rustc-dev-guide.rust-lang.org/borrow-check.html),
[region inference](https://rustc-dev-guide.rust-lang.org/borrow-check/region-inference.html),
and [drop elaboration](https://rustc-dev-guide.rust-lang.org/mir/drop-elaboration.html).
The origin/loan/fact vocabulary is intentionally close to
[Polonius](https://github.com/rust-lang/polonius), while the source-level
model is aligned with [Oxide](https://arxiv.org/abs/1903.00982) and
recent place/path models such as
[Place Capability Graphs](https://arxiv.org/abs/2503.21691). The
receiver/exclusivity direction is also consistent with Swift's ownership
manifesto, especially its [Law of Exclusivity](https://github.com/swiftlang/swift/blob/main/docs/OwnershipManifesto.md).

## Lowering

Ownership and borrow facts should be checked on the CFG ownership MIR
before lowering to lambda-G. Lowering may then erase most of the
source-level ownership types.

The lowerer now consumes checked Semantic MIR as the only body and
control-flow driver. MIR value delivery distinguishes a source `return`
from a block tail value, so expression blocks flow to the continuation
chosen by their caller without accidentally jumping to the function
return. Branches, switches, loops, source `return`, outer-loop
`break`/`continue`, handler scopes, abort-capable call splits, and
resumable perform splits are all represented in MIR before lambda-G
lowering. Typed AST nodes remain as expression, pattern, source-ID, and
type-lookup payloads, but there is no parallel AST statement lowering
path.

Lowering inserts explicit internal operations for deterministic local
scope drops and MIR-static assignment-replacement drops. Today those
lower to ordered lambda-G `free` glue for managed storage wrappers that
expose a `RawPtr`; the evaluator and VM track allocation records and make
double-free/use-after-free observable. The ownership pass classifies
conditional/open drop obligations, and lowering remains conservative
around moved roots until executable dynamic drop flags exist.
Retain/release accounting is not implemented. These operations are
effectful in the same sense as
allocation, raw memory access, and IO:

- do not memoize them;
- do not duplicate them through commoning;
- insert them on every normal and early exit path;
- account for CPS continuations, loop exits, handler abort paths, and
  closure capture boundaries.

lambda-G and the VM can continue to use pointer-shaped values as an
implementation detail while safe Talk APIs hide them.

## Regions

Region allocation should be expressed as a lexical handler for
`'alloc`:

```talk
withRegion {
	let bytes = Storage<Byte>(capacity: 1024)
	...
}
```

The handler owns the arena and releases everything at scope exit.
Native backends can lower such regions to stack allocation, bump
allocation, or arena allocation depending on escape analysis.

## FFI

FFI is explicit and unsafe. Safe values are lent to FFI through scoped
APIs:

```talk
func withCString<R>(s: Substring, body: (Unsafe.Pointer<Byte>) 'ffi -> R) 'alloc 'ffi -> R
func withUnsafeBytes<R>(s: Substring, body: (Unsafe.Pointer<Byte>, Int) 'ffi -> R) 'ffi -> R
func withUnsafeMutableBytes<R>(
	buf: MutableSlice<Byte>,
	body: (Unsafe.MutablePointer<Byte>, Int) 'ffi -> R
) 'ffi -> R
```

Pointers produced by these APIs cannot be returned, stored, or captured
by escaping closures. C-owned pointers must carry an explicit ownership
policy, such as borrowed, opaque, or owned with a known free function.

## Consequences

This keeps the surface language safe without pretending the compiler can
avoid pointers internally.

It also avoids reference counting everywhere. The preferred order is:

1. scalar and aggregate values in registers or stack slots;
2. unique owned storage with moves;
3. borrowed views for temporary access;
4. explicit clones for deep copies;
5. reference counting or copy-on-write only for types that choose shared
   storage;
6. cycle collection only if closure/cell cycles become a real language
   goal.

## Migration

1. Done: rename the current core allocation effect from `'heap` to
   `'alloc(allocation: Allocation)`.
2. Done for the safe boundary: keep the existing raw pointer
   implementation for core and `// unsafe` sources, while rejecting
   `RawPtr` and inline IR in safe sources.
3. In progress: introduce safe storage and view types. `Storage`,
   `ByteStorage`, and `Substring` exist, but low-level core internals
   still use `RawPtr`.
4. Done: change `String.slice` to return a borrowed `Substring` view.
5. Not started: change array and IO APIs to use storage and slices
   instead of `RawPtr`.
6. Done for the current source model: extend the post-type-check ownership and borrow pass.
   The source-near CFG ownership MIR, per-body CFG worklist joins,
   source-order use counts, internal facts, `needs_drop(T)`, use-before
   initialization checks, explicit capture modes, conservative escaping
   borrow rejection, and drop-plan elaboration are in place. Richer
   lifetime precision remains.
7. In progress: insert drop/release/free operations during lowering.
   Deterministic local scope and MIR-static assignment-replacement `free`
   glue is implemented; conditional/open drops and retain/release remain.
8. Done for `free`: the evaluator and VM use allocation records, reject
   double-free/use-after-free, and leave static storage frees as no-ops.
   Retain/release accounting is not implemented.
9. Not started: add unsafe FFI pointer lending APIs.
10. In progress: safe sources are gated away from `RawPtr`; replacing
    the remaining `// unsafe` raw APIs with safe array, IO, and FFI
    wrappers is still outstanding.
