# 15. Unsafe Code and Interop

Most TalkTalk programs never need the features in this chapter. Raw pointers and inline IR let low-level code bypass safety checks, while native library exports and embedding APIs connect TalkTalk to a host. Use the regular library first, and keep these boundaries small.

## The unsafe boundary

Raw-pointer operations and inline IR outside Core perform an intrinsic `'unsafe` effect. A lexical block acknowledges and discharges it:

```tlk norun
#unsafe {
    // Trusted raw storage operations belong here.
}
```

This is not a runtime handler. It is a static trust boundary: the programmer accepts obligations that ordinary type and ownership checking cannot prove. The compiler still checks the surrounding TalkTalk code, but it cannot prove that an arbitrary address is live, aligned, correctly typed, or within an allocation.

## Wrapping unsafe operations

An unsafe block is useful when it is the small implementation detail behind an ordinary typed operation. Keep pointer creation, arithmetic, access, and cleanup together. Validate lengths and tags before entering the block, return normal TalkTalk values, and do not let a raw pointer outlive the storage it addresses.

The wrapper's signature should state the ownership transition that the unsafe code actually performs. A read-only operation should borrow; an operation that stores a value should consume or clone it deliberately; an operation that writes through caller storage should use `mut`. Test the wrapper through its safe surface, including empty, boundary, and cleanup paths.

Unsafe code removes a check, not the invariant the check protected. If the wrapper claims a stronger guarantee than its implementation maintains, callers can be memory-unsafe even though they contain no `#unsafe` themselves.

## Inline IR

Trusted core code uses `#_ir(args...) { ... }` for primitives including scalar math and comparison, allocation and free, load and store, retain and copy, pointer offsets, fixed-array access, conversion, and host I/O.

Inline IR is compiler-facing syntax, not a general optimization escape hatch. It is unavailable to deterministic procedural macro services. Incorrect use can violate memory and ownership invariants even when surrounding TalkTalk code looks well typed.

## Emitting C

Generate a complete C program:

```sh
talk c program.tlk > program.c
```

Or let TalkTalk invoke a C compiler:

```sh
talk build --native program.tlk -o program
```

The generated C includes the TalkTalk runtime and implements the same finalized MIR semantics as the bytecode target.

## Exporting a native library

For a quick library build, select a public function. The prefix defaults to `talk`, and the generated header and manifest are optional:

```sh
talk c library.tlk --export add > library.c
```

For a distributable boundary, request the sidecar files and choose a namespace:

```sh
talk c library.tlk \
    --export add \
    --prefix example \
    --header library.h \
    --manifest library.manifest \
    > library.c
```

`--export` is repeatable. `--allow-effect EFFECT` declares which effects an exported boundary may perform. The generated header defines the versioned C call convention and lifecycle functions. The manifest maps TalkTalk export names to external symbols. A pure exported function is the simplest boundary; only allow effects whose generated runtime behavior the host intends to expose.

The arguments serve separate jobs: export selection belongs to the TalkTalk API, the prefix prevents link-time symbol collisions, and the two sidecars describe the C API and name mapping. Defaults keep inspection short while explicit paths make a shippable artifact reproducible.

## Native boundary obligations

A generated library permits one active invocation at a time. Initialize it before calling exports and tear it down after the last result is no longer needed. Successful result values remain valid until teardown. A trap or exit request is contained at the wrapper boundary and returned as a status rather than terminating the embedding process.

Ownership transfer at this boundary follows the generated header, not C's type system. Do not retain pointers into a result past teardown, fabricate tagged values, or call a wrapper with the wrong arity. Keep host conversion code in one place and test failure cleanup as well as successful calls.

## FFI embeddings

The repository contains three host-facing layers:

- `talk-ffi` - a C API for compiling and running TalkTalk
- `talk-swift` - a Swift package over the C API
- `wasm` - browser and JavaScript embedding of the bytecode compiler/runtime

Their READMEs and generated headers are the API references. These embeddings compile source through the same frontend and execute validated bytecode; they do not define a second language implementation.
