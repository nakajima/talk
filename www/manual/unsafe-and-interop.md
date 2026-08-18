# 15. Unsafe Code and Interop

Most TalkTalk programs never need the features in this chapter. Raw pointers and inline IR let low-level code bypass some safety checks, while the C interface lets TalkTalk call into a larger application. Use the regular library first, and keep these boundaries small.

## The unsafe boundary

Raw-pointer operations and inline IR outside Core perform an intrinsic `'unsafe` effect. A lexical block acknowledges and discharges it:

```tlk norun
#unsafe {
    // Trusted raw storage operations belong here.
}
```

This is not a runtime handler. It is a static trust boundary: the programmer accepts obligations that ordinary type and ownership checking cannot prove. Keep the block small and expose a typed safe operation around it.

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

The generated C links the static TalkTalk runtime and implements the same finalized MIR semantics as the bytecode target.

## Exporting a native library

The C command can emit host-callable wrappers for selected public functions:

```sh
talk c library.tlk \
    --export add \
    --prefix example \
    --header library.h \
    --manifest library.manifest \
    > library.c
```

`--export` is repeatable. `--allow-effect EFFECT` declares which effects an exported boundary may perform. The generated header describes the C ABI, and the manifest maps TalkTalk export names to external symbols.

Only use effect allowances the host actually supplies. A pure exported function is the simplest and safest boundary.

## FFI embeddings

The repository contains three host-facing layers:

- `talk-ffi` - a C API for compiling and running TalkTalk
- `talk-swift` - a Swift package over the C API
- `wasm` - browser and JavaScript embedding of the bytecode compiler/runtime

Their own READMEs and generated headers are the API references. These embeddings compile source through the same frontend and execute validated bytecode, rather than defining a second language implementation.

## Boundary design

A good unsafe or host boundary has four properties:

1. raw operations are confined to one small implementation,
2. the public signature uses ordinary TalkTalk values,
3. ownership transfer is explicit at the ABI edge, and
4. safe tests compare the boundary against a trusted reference behavior.

Unsafe code removes a check; it does not remove the invariant the check was protecting.
