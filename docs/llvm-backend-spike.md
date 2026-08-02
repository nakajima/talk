# LLVM backend spike

This spike answers what a full MIR-to-LLVM path looks like without adding a
Rust LLVM dependency.

## Pipeline

```text
TypedProgram
  -> MIR construction and ownership checking
  -> MIR optimization
  -> MIR register reuse
  -> public codegen model
  -> talk-llvm
  -> textual LLVM IR
  -> clang + native runtime translation unit
  -> executable
```

The target-neutral adapter in `src/backend/codegen.rs` exhaustively projects
every private MIR instruction and terminator into `talk::codegen`. The
`talk-llvm` workspace crate consumes that public model and owns textual IR
emission, its command-line interface, and the native pointer-ABI bridge. Adding
a MIR variant therefore makes the adapter fail to compile until the new
operation has a deliberate external form.

Language functions, basic blocks, calls, branches, block-argument copies, and
scalar operations are LLVM IR. Integer and floating-point arithmetic lower to
LLVM instructions directly. Operations that require the native runtime call
the bridge in `talk-llvm/src/llvm_runtime.c`.

The pointer ABI keeps `TalkValue` behind pointers at the C boundary. This
avoids encoding a platform-specific C aggregate calling convention in emitted
IR. LLVM language functions use one uniform signature:

```llvm
define void @talk_fnN(ptr %out, ptr %env, ptr %args)
```

The linked runtime owns allocation, checked memory operations, effects,
continuations, closures, cells, program globals, host IO, heap regions,
finalizers, and result rendering. The compiler passes its shared native C
prelude into `talk-llvm::Runtime`, so the C and LLVM targets reuse one runtime
implementation without duplicating source or introducing a dependency cycle.

## Commands

The main CLI treats unknown subcommands as Git-style extensions. With a
`talk-llvm` executable in `PATH`, it forwards the remaining `talk llvm ...`
arguments to that executable.

Render the module:

```sh
talk llvm program.tlk
```

Build an executable through Clang:

```sh
talk llvm build program.tlk -o program
```

Keep both intermediate files:

```sh
talk llvm build --keep program.tlk -o program
# program.ll
# program.runtime.c
```

With no source files inside a package, the command compiles the selected
package binary and its locked dependency graph. `--bin` selects a binary and
`--offline` uses only installed dependency sources. Pass `-` to compile stdin
from inside a package.

`--cc` selects the Clang-compatible driver, and `CLANG` is used when `--cc` is
absent.

## Coverage

The differential suite in `talk-llvm/tests/backend.rs` checks emitted IR
shape and compares native results with the VM. It covers the eight benchmark
programs and all nineteen complete programs in `tests/programs`, including
aggregates, strings, closures, mutable cells, resumed and aborting effects,
managed buffers, heap-region cycles, finalizers, globals, and host IO.

## Deliberate spike boundaries

- The emitted `.ll` links with a generated C runtime translation unit; it is
  not a self-contained module.
- Host compilation is supported. Cross-target runtime and libc discovery are
  not implemented.
- There is no LLVM library dependency, target-machine API, object emission API,
  debug metadata, or optimization-pipeline configuration.
- Aggregate representation still uses the native runtime's boxed arena shape.
  A production backend should consume MIR layout information directly.
- The command emits program entry points, not a stable native service ABI.
- Source and package CLI policy belongs to `talk-llvm`; the main `talk` binary
  only discovers and executes `talk-<command>` from `PATH`.

These boundaries isolate the production decisions while still exercising a
complete executable lowering of the current MIR vocabulary.
