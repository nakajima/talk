# Backend crate extraction plan

Status: implemented (ADR 0047)

## Summary

Move Talk's target-independent finalized MIR into one public `talk-mir` crate,
then make bytecode, C, and LLVM three concrete adapters over that MIR. Rename
the existing VM crate from `talk-runtime` to `talk-vm`. Rename the existing C
embedding crate from `talk-c` to `talk-ffi`, preserving its language-neutral C
interface and the current TalkSwift interface. Reuse the freed `talk-c` package
name for the C backend.

The end state is:

```text
TypedProgram
    -> compiler-owned MIR construction and ownership checking
    -> compiler-owned optimization, register allocation, and frame shaping
    -> talk-mir::Module
         |              |               |
         v              v               v
   talk-bytecode      talk-c         talk-llvm
         |
         v
      talk-vm
```

`talk-ffi` remains the language-neutral embedding interface. It depends on the
compiler, bytecode adapter, and VM so TalkSwift keeps formatting, analysis,
workspace, package, REPL, bytecode, and dynamic source-execution behavior.

## Decisions already made

1. Finalized MIR is the public target seam. There is no separate public
   `codegen` representation.
2. MIR construction and ownership analysis remain private compiler
   implementation.
3. Bytecode lowering is a separate `talk-bytecode` crate.
4. The bytecode format, validation, interpreter, memory, host IO, and execution
   accounting belong to `talk-vm`, which replaces `talk-runtime`.
5. The package name `talk-c` belongs to the C backend.
6. The existing C ABI facade becomes `talk-ffi` and is language-neutral rather
   than Swift-specific.
7. TalkSwift remains and preserves its current public Swift interface.
8. TalkSwift continues to use bytecode and the VM for dynamic execution, REPL,
   package run/test, and the self-hosted frontend.
9. C and LLVM share one native C runtime source owned by
   `talk-native-runtime`.
10. There is no generic backend trait or backend registry. Each real adapter
    consumes public MIR directly.
11. No new third-party dependencies are required.

## Goals

### Compiler locality

The `talk` compiler owns source semantics and target-independent lowering only:

- typed frontend output;
- MIR construction;
- ownership and initialization checking;
- layout selection;
- optimization;
- register allocation;
- frame-shaping facts;
- source-facing MIR diagnostics.

It does not own C emission, VM bytecode encoding, VM instruction fusion, or VM
execution wrappers.

### One real target seam

C, bytecode, and LLVM consume the same finalized MIR module. Adding a MIR
instruction or changing a layout contract must make all three adapters account
for the change through exhaustive matching.

### No duplicated IR

Delete the current public `talk::codegen` model and its exhaustive projection.
The final MIR data types are the public contract. The compiler's private
builder and analyses construct those types directly.

### Language-neutral embedding

`talk-ffi` owns a stable C ABI suitable for Swift and other C-compatible hosts.
TalkSwift is one binding over that interface, not its owner.

### Preserve behavior

The extraction must preserve:

- bytecode image bytes unless a separately reviewed format change is intended;
- the checked-in self-hosted frontend fixed point;
- VM behavior and resource accounting;
- generated C behavior;
- LLVM differential behavior;
- existing C ABI function symbols;
- the public TalkSwift source interface;
- existing CLI behavior, including `talk run`, `talk build`, `talk c`,
  `talk bytecode`, and `talk build --native`.

## Non-goals

This plan does not:

- serialize MIR;
- add a MIR compatibility version;
- add plugin loading for backend libraries;
- add a backend trait;
- make C replace VM execution in TalkSwift;
- add a host-callable native C library ABI for compiled Talk programs;
- change Talk language semantics;
- change the bytecode format;
- redesign the VM;
- remove the VM used by the self-hosted frontend;
- rename historical paths inside old ADRs, changelog entries, or commit reviews
  where the old names are historically correct;
- add dynamic-library distribution for `talk-ffi` in the first extraction.
  The C interface remains usable from other languages through the existing
  static library, and host `cdylib` packaging can be added independently.

## Target workspace

```text
talk-mir
    Public finalized MIR data and target-neutral metadata.

talk
    Frontend, TypedProgram, MIR production, ownership checking, optimization,
    register allocation, frame shaping, CLI, REPL, package compiler, and
    self-hosted frontend host.

talk-bytecode
    MIR-to-VM-bytecode adapter and compiled executable wrapper.

talk-vm
    VM bytecode model, bytecode encoding/decoding/validation, interpreter,
    memory, objects, IO, host values, budgets, and VM statistics.

talk-native-runtime
    Shared native C runtime source used by C and LLVM.

talk-c
    MIR-to-C adapter.

talk-llvm
    MIR-to-LLVM adapter and its existing command-line extension.

talk-ffi
    Language-neutral C ABI over the compiler, bytecode adapter, and VM.

talk-swift
    Swift binding over talk-ffi.

talk-static
    Existing static bytecode runner, updated to depend on talk-vm.

wasm
    Existing browser interface, updated to the new compiler/bytecode names.
```

The intended dependency directions are:

```text
                         +--------------------+
                         |      talk-mir      |
                         +--------------------+
                           ^        ^       ^
                           |        |       |
                  +--------+        |       +----------+
                  |                 |                  |
               talk            talk-bytecode       talk-c
                  |                 |                  |
                  |                 v                  v
                  +-------------> talk-vm     talk-native-runtime
                  |                                    ^
                  |                                    |
                  |                                talk-llvm
                  |
               talk-ffi
                  |
               talk-swift
```

More precisely:

- `talk-mir` depends only on the Rust standard library unless a currently
  existing workspace dependency is demonstrably required by the data contract.
- `talk-vm` does not depend on `talk` or `talk-mir`.
- `talk-bytecode` depends on `talk-mir` and `talk-vm`, never on `talk`.
- The `talk-c` library depends on `talk-mir` and `talk-native-runtime`, never on
  `talk`.
- `talk` may depend on `talk-bytecode` and `talk-vm`: the compiler host uses the
  VM for the self-hosted frontend, procedural macros, REPL, testing, bootstrap,
  and current convenience surfaces. This does not give target-specific
  lowering ownership back to the compiler.
- `talk-c` is an optional dependency of the root package's `cli` feature so the
  existing built-in C commands can remain unchanged without making C part of a
  `default-features = false` compiler build.
- `talk-llvm` depends on `talk` for source/package compilation, on `talk-mir`
  for its emitter interface, and on `talk-native-runtime` for native runtime
  source.
- `talk-ffi` depends on `talk`, `talk-bytecode`, and `talk-vm`.

## Public MIR interface

### Publication point

Only finalized target MIR is public:

```text
TypedProgram
    -> build MIR and check ownership
    -> optimize MIR
    -> compute pre-allocation parameter escape summaries
    -> register allocation
    -> stamp local layouts and frame-local sites under final numbering
    -> publish talk_mir::Module
```

The ordering matters. The current C path computes parameter escape summaries
before register allocation and stamps frame facts afterward. The single public
MIR producer must do this for every target so C does not need a compiler-private
prepass.

The unoptimized MIR used for debugging and ownership work remains private.
`talk mir --no-opt` may continue rendering that private form, but no target
adapter receives it.

### Data owned by `talk-mir`

Move the target-facing data vocabulary from `src/backend/mir` into
`talk-mir`:

- `LocalId`, `BlockId`, `FuncId`, and `LayoutId`;
- constants and operands;
- scalar operation and comparison kinds;
- the full instruction enum;
- terminators;
- blocks;
- functions;
- program/module entry and host-callable exports;
- global slot count;
- layout table;
- `Layout`, `Shape`, `FieldRepr`, and `SlotKind`;
- `LocalInfo`;
- parameter representation and return representation;
- frame-local construction sites;
- display names and type/member metadata needed by C, LLVM, and the VM;
- well-known runtime aggregate identities required for String and Storage.

The layout classifier itself stays in the compiler because it reads Talk types
and the type catalog. Only its resulting layout data belongs to `talk-mir`.
Likewise, ownership flow records, checker catalogs, source spans, type
substitutions, and compiler worklists do not enter the public crate.

### Executable symbol identity

Public MIR must not expose the complete source-level
`name_resolution::Symbol` enum. Define a compact executable identity containing
only facts that survive to targets:

```text
MirSymbol
    kind: Struct | Enum | Effect | Protocol
    module: u16
    local: u32
```

The compiler performs the single source-symbol-to-MIR-symbol translation when
it emits MIR. Display names are metadata, never identity. C and LLVM can intern
these identities for generated tables. The bytecode adapter maps aggregate
identities structurally to `talk_vm::symbol::Symbol` and interns effect
identities in the VM module.

Every current `Symbol` occurrence in `src/backend/mir` falls into one of four
buckets, and only the first survives into the public crate:

1. Instruction operands: `PushHandler.effect`, `FindHandler.effect`, and
   `ExistentialPack.protocol`. These become `MirSymbol` at emission.
2. Layout and aggregate identities plus runtime metadata (struct/enum
   identities behind the layout table, display names, String and Storage).
   These become `MirSymbol`-keyed metadata on the public module. Aggregate
   construction is already layout-keyed (`Aggregate { layout, tag, .. }`), so
   no instruction carries a Struct or Enum symbol today.
3. Well-known type comparisons (`Symbol::Int`, `Symbol::RawPtr`, and similar)
   in the builder and classifier. These are compiler-private decisions; only
   the String and Storage identities they feed are published.
4. Builder-private construction indexes: callable and instance keys, global
   slot maps, catalog indexes, pattern bindings, type parameters, and
   substitutions. These never leave the compiler. Functions are already
   `FuncId` and globals are already `u32` slot indices in the data
   definitions, so no instruction position needs a new identity type beyond
   bucket 1.

### Interface invariants

A compiler-produced public module guarantees:

1. every function, block, local, layout, and global reference is in range;
2. every block has one terminator;
3. block argument counts match block parameters;
4. all source ownership and cleanup decisions are already explicit;
5. every executable instance is monomorphic or is an intentional check-only
   trap form already accepted by the current pipeline;
6. layout IDs, field offsets, member layouts, local layouts, parameter
   representations, return representations, and frame sites are final;
7. function local tables use final register numbering;
8. host-callable exports name existing wrapper functions;
9. display metadata and runtime identities agree with layout identities;
10. target adapters need no `TypedProgram`, type catalog, parser node, source
    span, or name-resolution query.

The module is trusted in-process data. Do not add serialization-grade MIR
validation, a fixture-only builder framework, or a second proof wrapper. The
compiler's existing construction checks and tests establish the invariants.
Adapters return target errors for malformed manually constructed values, but
they do not replay source semantic checking.

### Compiler interface

Replace target-specific methods on `Driver<Typed>` with one public MIR
publication interface, conceptually:

```rust
pub enum MirEntry<'a> {
    Script,
    Named(&'a str),
    Exports {
        names: &'a [String],
        allowed_effects: &'a [String],
    },
}

pub struct MirOutput {
    pub module: talk_mir::Module,
    pub optimizations: OptimizationStats,
}

impl Driver<Typed> {
    pub fn compile_mir(&self, entry: MirEntry<'_>) -> Result<MirOutput, CompileError>;
}
```

Exact ownership and lifetime syntax may differ, but the semantic surface should
not. `compile_mir` is the only target compilation interface.

Keep compiler-owned operations in `talk`:

- `check_ownership`;
- unoptimized and optimized MIR rendering;
- source-location rendering for MIR construction failures.

Move or remove target-specific compiler interfaces:

- `compile_executable` moves to composition with `talk-bytecode`;
- `compile_service` moves to `compile_mir(MirEntry::Exports)` plus
  `talk_bytecode::compile`;
- `execute_module` and `execute_image` move out of `compiling::driver`;
- `render_c` and `render_c_service` become `compile_mir` plus
  `talk_c::emit`;
- `codegen` and `PackageProject::codegen_binary` are replaced by MIR-named
  equivalents.

The root CLI, REPL, test harness, bootstrap, package runner, procedural macro
host, wasm facade, and `talk-ffi` compose these concrete interfaces. They do
not require a backend trait.

## Adapter interfaces

### `talk-bytecode`

`talk-bytecode` owns the complete MIR-to-VM adapter:

- current `src/backend/lower.rs`;
- current `src/backend/checked_indexed_load.rs`;
- target constant, trap, static-data, effect, argument, and switch pools;
- block linearization and target patching;
- mapping MIR layouts and symbols to VM layouts and symbols;
- bytecode-only optimization statistics;
- the compiled executable wrapper that combines a VM module, rendering names,
  and bytecode-adapter statistics.

Conceptual interface:

```rust
pub fn compile(module: &talk_mir::Module) -> Result<Executable, CompileError>;

pub struct Executable {
    // private talk_vm::Module, display metadata, and backend statistics
}
```

`Executable` owns the current convenience behavior:

- `encode_bytecode`;
- bytecode rendering;
- ordinary execution;
- host-export execution;
- execution with VM statistics;
- access to bytecode-adapter statistics.

Compiler optimization counts, bytecode-adapter counts, and VM execution counts
stay with their owning modules:

```text
MirOutput
    compiler optimizations

Executable
    bytecode adapter optimizations

VmStats
    VM execution statistics
```

A CLI or profiling caller may render the three together, but
`talk-bytecode::compile` receives only `talk_mir::Module` and does not acquire a
dependency on compiler-owned `MirOutput`. The current `checked_indexed_load`
count must not masquerade as a compiler-owned MIR pass after the extraction.

### `talk-vm`

Rename the existing `talk-runtime` package and crate to `talk-vm` /
`talk_vm`. It owns:

- `Insn`, `Chunk`, `Module`, constants, memory kinds, layouts, and symbols;
- bytecode format versions;
- encode and decode;
- validation of byte images;
- interpreter frames, closures, continuations, effects, and exports;
- memory allocations and pointer provenance;
- heap objects, cells, and regions;
- host IO;
- budgets;
- `HostValue`, `RunOutcome`, and value rendering;
- VM statistics and profiling.

It does not know MIR and does not depend on `talk-mir`.

There are two trust paths:

- `talk-bytecode` constructs an in-memory module under compiler invariants;
- `talk_vm::Module::decode_bytecode` treats bytes as untrusted and validates
  before execution.

Keep these paths distinct. Do not move MIR lowering into `talk-vm`, and do not
make decoded bytes trusted because the compiler can also construct modules.

The existing `talk-static` C entry point may keep its
`talk_runtime_run` exported symbol for compatibility while its Rust dependency
changes to `talk-vm`.

### `talk-c`

After the old embedding package moves to `talk-ffi`, reuse `talk-c` for the C
backend. Move:

- `src/backend/c.rs`;
- its focused emitter tests;
- its target error type.

Conceptual interface:

```rust
pub struct Artifact {
    pub source: String,
}

pub fn emit(module: &talk_mir::Module) -> Result<Artifact, Error>;
```

Returning an artifact rather than driving a host compiler keeps target
translation separate from CLI/toolchain policy. The root CLI continues to own:

- `--cc`;
- `--target` and Zig selection;
- `--cflag`;
- output paths;
- scratch files;
- `--keep-c`.

The `talk-c` package has no dependency on `talk`. Its tests may use `talk` as a
dev-dependency for source-to-MIR and differential fixtures.

The current generated-program contract remains unchanged: one self-contained C
translation unit with `main`. A stable host-callable C library ABI for compiled
Talk programs is explicitly outside this extraction.

### `talk-llvm`

Change the LLVM emitter to consume `talk_mir::Module` directly. Remove:

- `talk::codegen` imports and re-exports;
- the copied codegen model;
- `Runtime::native_prelude`.

Keep `talk-llvm`'s current artifact interface and CLI behavior. It may depend on
`talk` for source and package compilation, while its emitter module depends
only on `talk-mir` and `talk-native-runtime` concepts.

### `talk-native-runtime`

Move `src/backend/c_prelude.c` into a small first-party crate. Its interface can
remain narrow:

```rust
pub fn source() -> &'static str;
```

This module earns its seam because C and LLVM are two real consumers of one
large runtime implementation. Neither backend should depend on the other to
obtain it.

`talk-llvm/src/llvm_runtime.c` remains LLVM-owned because it is the LLVM
pointer-ABI bridge, not the shared native runtime itself.

## `talk-ffi` and TalkSwift

### Package and artifact naming

Rename the current `talk-c` embedding package to `talk-ffi`:

```text
talk-c/Cargo.toml             -> talk-ffi/Cargo.toml
talk-c/src/lib.rs             -> talk-ffi/src/lib.rs
talk-c/include/talk_c.h       -> talk-ffi/include/talk_ffi.h
talk-c/README.md              -> talk-ffi/README.md
```

Use package and crate name `talk-ffi` / `talk_ffi`, producing
`libtalk_ffi.a`. The Swift binary artifact becomes `TalkFFI.xcframework`, and
the internal Swift system module becomes `CTalkFFI`.

The public Swift module remains `TalkSwift`, and its public Swift types and
methods remain unchanged.

### C interface compatibility

Preserve every existing exported `talk_*` function name and its argument,
return, ownership, and error behavior. Renaming the package and header must not
silently change the ABI.

Add an explicit interface version distinct from the compiler version:

```c
#define TALK_FFI_ABI_VERSION 1
uint32_t talk_ffi_abi_version(void);
```

Document in `talk_ffi.h` and the README:

- ownership of every returned buffer and opaque handle;
- the exact matching free function;
- how long borrowed `TalkStringRef` and view data remain valid;
- callback lifetime and synchronous-callback rules;
- handle thread-affinity;
- UTF-8 requirements;
- panic containment;
- status and error conventions.

Keep the existing `catch_unwind` protection at every exported entry path.

### Runtime behavior

`talk-ffi` continues to expose the complete existing behavior:

- formatter and highlighter;
- one-shot checking and execution;
- bytecode rendering and bytecode image compilation;
- package creation, installation, run, and test;
- package source-provider callbacks;
- workspace diagnostics and editor queries;
- REPL evaluation, type queries, completion, and input continuation;
- all typed result handles and free functions.

Internally, source execution changes from compiler-private backend calls to:

```text
source -> talk::compile_mir -> talk_bytecode::compile -> talk_vm::execute
```

This is an ownership change, not a behavior change.

### TalkSwift migration

Update implementation-only names:

```text
CTalkC                         -> CTalkFFI
import CTalkC                  -> import CTalkFFI
TalkC.xcframework              -> TalkFFI.xcframework
TalkC.xcframework.zip          -> TalkFFI.xcframework.zip
libtalk_c.a                    -> libtalk_ffi.a
talk_c.h                       -> talk_ffi.h
talkCReleaseURL                -> talkFFIReleaseURL
talkCReleaseChecksum           -> talkFFIReleaseChecksum
```

Do not rename public Swift declarations. Existing TalkSwift tests should build
without source changes beyond the private C module import.

The root `Package.swift`, `talk-swift/Package.swift`, module map,
`talk-swift/scripts/build-xcframework.sh`, CI workflow, release workflow, and
TalkSwift README all move together in one stage.

### Multi-language readiness

A C interface is the shared language seam. Do not add language-specific Rust
entry points. Add a small C smoke client that includes `talk_ffi.h`, links the
host static library, calls representative one-shot and handle APIs, and frees
all results. That test proves the interface independently of Swift and becomes
the template for future Python, Kotlin/Native, C#, or other bindings.

Host dynamic-library packaging is a follow-up. It does not block other hosts
that can link the static C library, and it should not be added to the iOS crate
type list without validating every Apple target.

## Error and trust ownership

### Compiler errors

MIR construction failures retain source spans and are rendered by `talk`:

- source-invalid constructs that survived recovery;
- ownership, move, borrow, initialization, or cleanup diagnostics;
- entry/export selection failures;
- violated compiler invariants.

### Adapter errors

C, bytecode, and LLVM errors do not depend on parser spans or TypedProgram.
They identify:

- malformed public MIR supplied manually;
- target representability failures;
- target-internal invariant failures.

A compiler-produced finalized MIR module should not receive a capability
rejection from one parity backend. ADR 0037's completeness requirement remains
in force.

### VM runtime errors

Runtime failures remain owned by `talk-vm`:

- malformed decoded images;
- invalid dynamic memory operations;
- instruction or memory budgets;
- host IO failures;
- traps;
- resource-balance failures.

### FFI errors

`talk-ffi` translates compiler, adapter, and VM errors into the existing C
status/result shapes. It catches Rust panics and never unwinds across C.

## Detailed migration stages

Every stage must build and test independently. Temporary compatibility
re-exports are allowed within a stage sequence, but none remain in the final
state.

### Stage 0: Record the architecture and baseline behavior

#### Work

1. Add an ADR following ADR 0046 that amends ADR 0034's implementation shape:
   - three adapters justify a public finalized MIR seam;
   - bytecode remains the parity execution target but is no longer private
     compiler implementation;
   - the VM and bytecode adapter are separate modules;
   - in-process MIR remains trusted and unserialized;
   - `talk-ffi` remains VM-backed.
2. Record current package and target dependency graphs with `cargo tree`.
3. Record current nonblank production line counts for target-neutral compiler,
   C adapter, bytecode adapter, VM, LLVM, and FFI separately.
4. Record the current exported `talk_*` C symbol list from `libtalk_c.a` as the
   ABI migration oracle.
5. Inventory every caller of the `Driver<Typed>` backend methods
   (`compile_executable`, `compile_service`, `render_c`, `render_c_service`,
   `codegen`, `render_mir`) so no consumer is discovered mid-stage: CLI, REPL,
   LSP server, test harness, bootstrap, package runner, procedural macro host,
   wasm, `talk-ffi`, and benches.
5. Run and record the baseline validation commands listed below.

#### Acceptance

No production behavior changes. The plan and ADR agree on ownership and names.

### Stage 1: Rename `talk-runtime` to `talk-vm`

#### Files

- `talk-runtime/` -> `talk-vm/`;
- package name `talk-runtime` -> `talk-vm`;
- Rust imports `talk_runtime` -> `talk_vm`;
- root features and path dependencies;
- `talk-static`, `talk-c` before its FFI rename, `talk-llvm` tests, wasm, tests,
  scripts, and current documentation.

#### Rules

- This is a mechanical rename only.
- Do not move MIR lowering into the VM.
- Do not change bytecode format constants or encoded bytes.
- Do not rename historical references in old ADRs or commit reviews when they
  describe the old repository accurately. Add current-name notes where needed.
- Keep the `talk_runtime_run` C symbol in `talk-static` unless a separate ABI
  decision changes it.

#### Acceptance

- Direct VM tests pass under package `talk-vm`.
- Workspace tests pass.
- `talk bootstrap --check` reports the checked-in artifact is current.
- A before/after encoded fixture is byte-identical.

### Stage 2: Rename the embedding crate to `talk-ffi`

#### Files

- move `talk-c/` to `talk-ffi/`;
- update workspace members and Cargo lockfile;
- rename the Rust crate and static archive;
- rename and document the public header;
- update root and nested Swift package manifests;
- update `talk-swift/Sources/CTalkC` to `CTalkFFI`;
- update the XCFramework build script;
- update CI and release workflow names, paths, release asset, URL stamping, and
  checksum variables;
- update current READMEs and current parity documentation.

#### Rules

- Preserve all existing `talk_*` exported functions.
- Preserve public TalkSwift source declarations and behavior.
- Do not change result layouts while renaming.
- Keep VM-backed execution.
- Add the ABI version and C smoke test, but do not otherwise redesign the C
  interface in this stage.

This stage is a mechanical rename with exactly two intentional additive
exceptions: the new `talk_ffi_abi_version` symbol and the C smoke client. The
symbol oracle therefore changes by design (`+1` symbol), and both additions are
covered by their own acceptance checks so the rename itself remains
behavior-preserving and reviewable as such.

#### Acceptance

- `cargo test -p talk-ffi --locked` passes.
- The exported `talk_*` symbol oracle matches, plus the new ABI-version symbol.
- The host C smoke client compiles, links, runs, and frees all results.
- `swift test` passes against `target/debug/libtalk_ffi.a`.
- the XCFramework builds and TalkSwift tests pass against it;
- the iOS simulator build passes.

At this point the `talk-c` package name is free.

### Stage 3: Introduce `talk-mir` without changing targets

This is the highest-risk structural stage and should be split into small green
commits. `src/backend/mir/mod.rs` is roughly 10,000 lines with around 150
`Symbol` uses, so the split is larger than "move data definitions" suggests;
plan commits accordingly.

The `Symbol` cut must come first. Instruction data carrying
`name_resolution::Symbol` (`PushHandler`, `FindHandler`, `ExistentialPack`)
cannot move into `talk-mir` at all until those fields become `MirSymbol`,
because `talk-mir` cannot depend on the compiler. Perform the translation
while everything is still in one crate, where the change is a type substitution
with full compiler and test feedback, then move the cleaned definitions.

#### Stage 3A: Cut instructions to `MirSymbol`, then move data definitions

1. Define `MirSymbol` in the compiler and translate at MIR emission (bucket 1
   in "Executable symbol identity"). Keep every other `Symbol` use
   compiler-private. This commit touches the instruction enum, the builder
   emission points, the renderers, and all three targets' reads of those
   fields, and it is the last commit in which a mistake is cheap to find.
2. Create `talk-mir`.
3. Move instruction, terminator, block, function, program, local, and layout
   data definitions into it.
4. Split data definitions out of `src/backend/mir/layout.rs`; keep type/catalog
   classification in the compiler.
5. Make compiler MIR construction, verification, optimization, register
   allocation, escape analysis, and renderers import the shared types.
6. Keep private compiler-only helper state and algorithms in `talk`.
7. Use temporary re-exports under `crate::backend::mir` to keep changes
   mechanical while callers migrate.

Acceptance: all existing targets still consume the same values and workspace
tests pass.

#### Stage 3B: Complete the public module

1. Move layout/aggregate identity metadata onto `MirSymbol` keys (bucket 2 in
   "Executable symbol identity").
2. Move display/type/member metadata production into the compiler's MIR output.
3. Add exports, runtime aggregate identities, final local layouts,
   parameter/return representations, and frame sites to the public contract.
4. Make the one finalized producer compute parameter summaries before register
   allocation and stamp frames after it.
5. Add `MirEntry`, `MirOutput`, and `Driver<Typed>::compile_mir`.
6. Add package-level MIR publication for selected binaries.
7. Add interface tests proving a source fixture publishes every target-required
   fact.

Acceptance: C, bytecode, and LLVM can be driven from the public output without
reading `TypedProgram` or compiler-private MIR modules.

#### Stage 3C: Delete the duplicate codegen model

1. Change LLVM to consume `talk-mir`.
2. Remove `src/codegen.rs`.
3. Remove `src/backend/codegen.rs`.
4. Remove `talk::codegen` and `codegen_binary`.
5. Update `docs/llvm-backend-spike.md` to describe public MIR.

Acceptance:

```sh
rg "crate::codegen|talk::codegen|backend::codegen" src talk-llvm
```

returns no production matches. Repeat the repository-wide form after the C and
bytecode crates exist.

### Stage 4: Extract `talk-bytecode`

#### Work

1. Create `talk-bytecode` with dependencies on `talk-mir` and `talk-vm`.
2. Move bytecode lowering and target fusion out of `src/backend`.
3. Move `Executable`, target execution conveniences, and bytecode-adapter
   statistics.
4. Convert runtime symbol mapping to consume MIR symbols and metadata.
5. Change root CLI run/build/image/bytecode paths to compose
   `compile_mir` and `talk_bytecode::compile`.
6. Change bootstrap and procedural macro compilation to the same composition.
7. Change REPL, testing, package execution, LSP, benches, wasm, and `talk-ffi`.
   The LSP server is expected to need only `check_ownership` and diagnostics,
   which stay in the compiler; confirm against the Stage 0 caller inventory
   rather than assuming it.
8. Move focused lowering and fusion tests into `talk-bytecode`.
9. Keep source-level differential and integration tests at the workspace level.
10. Remove bytecode-specific imports and types from the compiler MIR module.

#### Acceptance

- `talk-bytecode` has no dependency on `talk`.
- `talk-vm` has no dependency on `talk-mir`.
- the self-hosted frontend artifact remains byte-identical;
- run, build, image, service export, procedural macro, REPL, package, wasm, and
  TalkSwift tests pass;
- VM allocation/object balance behavior is unchanged;
- bytecode disassembly snapshots are unchanged unless separately reviewed.

### Stage 5: Extract the shared native runtime

#### Work

1. Create `talk-native-runtime`.
2. Move `src/backend/c_prelude.c` into it.
3. Change the still-internal C emitter to consume its source.
4. Change LLVM to consume the same source directly.
5. Remove `talk::codegen::native_runtime_c` and any equivalent compiler-owned
   runtime accessor.

#### Acceptance

- C and LLVM generated programs pass differential tests.
- There is one tracked copy of the shared prelude.
- Neither backend depends on the other.
- `talk` no longer embeds the native C runtime source.

### Stage 6: Create the new `talk-c` backend

#### Work

1. Create package `talk-c` with dependencies on `talk-mir` and
   `talk-native-runtime`.
2. Move `src/backend/c.rs` and its focused tests.
3. Give it a target-local `Error` with no parser `Span` dependency.
4. Expose `emit(&talk_mir::Module)`.
5. Add it as an optional root dependency enabled by `cli`.
6. Change `talk c` and `talk build --native` to call `compile_mir` followed by
   `talk_c::emit`.
7. Keep host compiler selection and filesystem/toolchain policy in
   `src/bin/talk.rs`.
8. Update C differential tests and the corpus sweep to exercise the external
   crate interface.

#### Acceptance

- `talk-c` production dependencies contain neither `talk` nor `talk-vm`.
- C emission has no access to TypedProgram, source spans, the type catalog, or
  name resolution.
- GCC and Clang corpus sweeps pass.
- cross-target C compilation tests retain their current coverage.
- `talk build --native` remains behaviorally compatible.

### Stage 7: Align LLVM and remove compatibility residue

Although LLVM first moves to public MIR in Stage 3C, this stage removes any
remaining transitional compatibility:

1. simplify `talk-llvm::emit` to accept the complete MIR module;
2. remove generic symbol plumbing made unnecessary by `MirSymbol`;
3. source display and runtime identities only from MIR metadata;
4. remove the runtime-prelude argument;
5. update LLVM docs and focused emission tests;
6. verify its command-line extension still supports packages, stdin, named
   entries, emission, and build.

Acceptance: LLVM's library emitter needs only MIR plus native runtime source,
and all differential programs agree with the VM.

### Stage 8: Consolidate the compiler module and documentation

#### Work

1. Move the remaining target-independent `src/backend` implementation under
   `src/compiling/mir` or another compiler-owned name chosen in the ADR:
   - MIR builder;
   - ownership verifier;
   - release planning;
   - layout classifier;
   - entries and glue generation;
   - optimization;
   - register allocation;
   - escape/frame shaping.
2. Delete target-specific files from the compiler tree.
3. Update current architecture documentation, backend parity docs, profiling
   scripts, size reports, CI labels, and READMEs.
4. Keep historical ADR and commit-review paths unchanged where they describe
   history; add a superseding current ADR rather than rewriting the record.
5. Report final production, test, comment, and generated-source line counts by
   module.

#### Acceptance

The compiler tree contains no C emitter, native prelude, bytecode lowering, or
VM executable wrapper.

## Test strategy

### Per-crate tests

| Module | Required focused tests |
| --- | --- |
| `talk-mir` | layout/data helpers, debug rendering, identity equality, target-required fixture shapes |
| `talk-vm` | encode/decode/validation, interpreter, memory, objects, IO, budgets, stats |
| `talk-bytecode` | lowering, pools, branches, unwind patching, layout mapping, fusion, malformed MIR errors |
| `talk-native-runtime` | source availability and native smoke compilation through consumers |
| `talk-c` | focused emitted-C structure and target errors |
| `talk-llvm` | focused LLVM emission and runtime bridge |
| `talk-ffi` | C ABI handles, errors, callbacks, panic containment, symbol oracle, C smoke client |
| `talk-swift` | existing Swift behavior without public source changes |

### Cross-module handshake tests

Use real producer output rather than hand-maintained duplicate fixtures for the
important seams:

1. source -> finalized public MIR;
2. public MIR -> bytecode -> VM result;
3. public MIR -> C -> native result;
4. public MIR -> LLVM -> native result;
5. source -> `talk-ffi` -> VM result;
6. `talk-ffi` -> TalkSwift value/result translation.

Internal MIR unit fixtures remain useful for optimizer and adapter edge cases,
but black-box source fixtures remain the semantic oracle.

### Mandatory repository gates

Run after every stage that can affect them:

```sh
cargo build --workspace --locked
cargo test --workspace --all-targets --locked
target/debug/talk bootstrap --check
./scripts/c-backend-sweep.sh
./scripts/c-backend-sweep.sh --cc clang
cargo test -p talk-llvm --locked
cargo test -p talk-ffi --locked
swift test -Xlinker -L -Xlinker "$PWD/target/debug"
./talk-swift/scripts/build-xcframework.sh
swift package reset
swift test
xcodebuild -scheme TalkSwift -destination "generic/platform=iOS Simulator" build
git diff --check
```

Use the just-built binary for the bootstrap command, for example
`target/debug/talk bootstrap --check`, so PATH cannot select a stale compiler.

### Dependency gates

Add CI checks or repository assertions for:

```text
talk-vm          must not depend on talk or talk-mir
talk-bytecode    must not depend on talk
talk-c           must not depend on talk or talk-vm
talk-mir         must not depend on talk, talk-vm, or a target adapter
talk-native-runtime must not depend on a backend
talk-ffi         may depend on talk, talk-bytecode, and talk-vm
talk-llvm        may depend on talk for its CLI, but its emitter consumes MIR
```

## Compatibility policy

### Preserved

- Talk language behavior;
- bytecode wire format and version;
- checked-in frontend artifact bytes;
- all current `talk_*` C function symbols and result contracts;
- public TalkSwift declarations and behavior;
- CLI command spelling and behavior;
- native generated-program behavior;
- LLVM command behavior.

### Intentionally renamed

- Rust package/crate `talk-runtime` / `talk_runtime` -> `talk-vm` /
  `talk_vm`;
- embedding package/crate `talk-c` / `talk_c` -> `talk-ffi` / `talk_ffi`;
- embedding header and binary artifact names from C-specific to FFI-specific;
- internal Swift C module `CTalkC` -> `CTalkFFI`;
- existing C backend package name becomes `talk-c`.

### Removed

- public `talk::codegen`;
- private-to-public codegen projection;
- compiler-owned C emitter;
- compiler-owned bytecode lowering and target fusion;
- compiler-driver ownership of VM executable types;
- compiler ownership of the native C prelude.

## Risks and mitigations

### Bootstrap drift

Moving lowering code can accidentally alter deterministic pool or function
ordering.

Mitigation: require `talk bootstrap --check` after the MIR and bytecode stages;
do not regenerate the artifact during a supposedly mechanical extraction.

### MIR contract accidentally exposes frontend internals

Moving current types mechanically could pull source symbols, spans, type
catalogs, or checker state into `talk-mir`.

Mitigation: define `MirSymbol`, target metadata, and the forbidden dependency
list before moving adapters. `talk-mir` cannot depend on `talk`.

### C loses frame-shaping facts

The current public codegen model is too small for the C backend, and current
frame shaping runs only on the C path.

Mitigation: make pre-allocation summaries and post-allocation frame stamping
part of the one finalized MIR publication path before extracting C.

### VM/compiler cycle

If `talk-bytecode` depends on `talk`, `talk` cannot use it for bootstrap,
procedural macros, REPL, or testing.

Mitigation: `talk-bytecode` depends only on `talk-mir` and `talk-vm`.

### FFI rename breaks Swift packaging

Package names, archive names, module maps, XCFramework names, release URLs, and
checksums are spread across Cargo, two Swift manifests, scripts, CI, and release
workflows.

Mitigation: perform the FFI rename as one behavior-preserving stage, compare
exported symbols, and test both host-static and XCFramework resolution modes.

### Historical documentation becomes misleading

Blind replacement of `talk-runtime` and `talk-c` would make historical ADRs
and commit reviews inaccurate.

Mitigation: update current docs and add a superseding ADR; retain historical
names where they describe the repository at that time.

### Target errors become source diagnostics

External adapters no longer have compiler spans, which can tempt callers to
wrap all adapter errors as source failures.

Mitigation: keep compiler, adapter, VM, and FFI error types distinct. The
compiler locates source errors before publishing MIR; adapter invariant errors
remain target errors.

### Scope expands into a native service ABI

Because the C backend and C FFI are being renamed together, it is easy to
conflate generated C with the language-neutral embedding interface.

Mitigation: keep `talk-c` and `talk-ffi` independent. TalkSwift remains
VM-backed. A native host-callable ABI for compiled Talk modules requires a
separate decision.

## Completion criteria

The extraction is complete when all of the following hold:

1. `talk-mir` is the only public target input model.
2. `src/codegen.rs` and `src/backend/codegen.rs` do not exist.
3. C, bytecode, and LLVM consume `talk_mir::Module` only.
4. No target adapter imports TypedProgram, source AST, parser spans, type
   catalogs, or name-resolution data.
5. `talk-bytecode` owns MIR-to-bytecode lowering and target fusion.
6. `talk-vm` owns the bytecode format, validation, and execution, with no MIR
   dependency.
7. `talk-c` owns C emission and has no compiler dependency.
8. `talk-native-runtime` is the single owner of the shared C runtime source.
9. `talk-ffi` owns every exported language-neutral `talk_*` C function.
10. TalkSwift links `TalkFFI.xcframework` and preserves its public interface.
11. The compiler source tree contains only target-neutral MIR work.
12. Existing CLI commands remain available.
13. The checked-in frontend artifact remains at a verified fixed point.
14. Workspace, C differential, LLVM differential, C ABI, Swift host,
    XCFramework, and iOS simulator gates all pass.
15. No new third-party dependency was added.

## Proposed merge sequence

Keep each numbered item independently green:

1. ADR, baseline measurements, and ABI symbol oracle.
2. Mechanical `talk-runtime` -> `talk-vm` rename.
3. Mechanical `talk-c` embedding -> `talk-ffi` rename, including TalkSwift
   packaging.
4. `MirSymbol` instruction cut, then `talk-mir` data definitions with private
   compiler re-exports.
5. Complete finalized MIR metadata and `compile_mir`.
6. Move LLVM to public MIR and delete `talk::codegen` plus its projection.
7. Extract `talk-bytecode` and migrate all VM-backed callers.
8. Extract `talk-native-runtime`.
9. Create the new `talk-c` backend and migrate C CLI paths.
10. Remove compatibility re-exports, consolidate compiler MIR files, update
    current documentation, and publish final size/dependency accounting.

Do not combine the VM rename, FFI packaging rename, public MIR conversion, and
bytecode extraction in one change. Each has a different regression oracle, and
keeping them separate makes failures attributable and rollback safe.
