# talk-llvm

LLVM code generation for Talk's backend IR.

The crate consumes `talk::codegen`, lowers every instruction and terminator to
textual LLVM IR in `emit.rs`, and owns the `talk-llvm` executable plus the C
pointer-ABI bridge used by generated modules.

The compiler projects private MIR into the public target-neutral model in
`src/backend/codegen.rs`. Native runtime policy remains with the compiler and
is provided through `Runtime::native_prelude`, so the C and LLVM targets share
one runtime implementation without duplicated source.

Install `talk-llvm` in `PATH` and the main CLI discovers it as `talk llvm`:

```sh
cargo install --path talk-llvm
talk llvm program.tlk
talk llvm build program.tlk -o program
```

With no source files inside a package, `talk llvm` compiles the package binary
and its locked dependency graph. Use `--bin NAME` to select among multiple
binaries and `--offline` to prohibit dependency fetching. This works from any
directory inside the package. Pass `-` explicitly to compile standard input
instead.
