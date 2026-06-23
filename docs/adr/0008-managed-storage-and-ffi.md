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

The initial borrow checker should run after type checking over the
typed AST. It should use `TypeOutput`, resolved symbols, member
resolution, mutation information, and capture information.

It should compute:

- copy, move, borrow, and mutable-borrow uses;
- use-after-move diagnostics;
- escaping-borrow diagnostics;
- closure capture modes;
- drop obligations for non-copy owned values.

Lexical scopes and structured control flow are sufficient for the
first implementation. Borrowed values should not be storable in owned
heap data until the lifetime model is explicit enough to describe that
soundly.

## Lowering

Ownership and borrow facts should be checked before lowering to
lambda-G. Lowering may then erase most of the source-level ownership
types.

Lowering must still insert explicit internal operations for drops,
releases, retains, and frees. These operations are effectful in the
same sense as allocation, raw memory access, and IO:

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

1. Rename the current core allocation effect from `'heap` to
   `'alloc(allocation: Allocation)`.
2. Keep the existing raw pointer implementation temporarily so current
   examples continue to run.
3. Introduce safe storage and view types.
4. Change `String.slice` to return a borrowed view.
5. Change array and IO APIs to use storage and slices instead of
   `RawPtr`.
6. Add the post-typecheck ownership and borrow pass.
7. Insert drop/release/free operations during lowering.
8. Replace the VM bump-only memory with allocation records where free
   and release have observable correctness.
9. Add unsafe FFI pointer lending APIs.
10. Deprecate then remove public `RawPtr`.
