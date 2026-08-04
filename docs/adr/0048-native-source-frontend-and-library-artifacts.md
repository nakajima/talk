# ADR 0048: One native source frontend and native library artifacts

Status: accepted; implemented (2026-08-03) with one amendment below

Amendment (2026-08-03): wasm32 is carved out of section 1's "unsupported
targets fail" rule. Its toolchain cannot compile the generated frontend C
(no libc sysroot under wasm-pack), so wasm32 executes the verified
bootstrap bytecode in the VM as its only production path. This is a
per-target port of the same fixed-point frontend program, not a
selectable strategy: no other target may choose bytecode, and the
native/bytecode agreement tests pin the two executions together.

Amends ADR 0043's production execution mechanism and ADR 0047 sections 2 and
5. The Talk sources, bootstrap fixed point, ABI validation boundary, public MIR
seam, and `talk-ffi` ownership remain unchanged.

## Context

ADR 0043 moved the canonical lexer and parser into Talk and used a checked-in
bytecode artifact to break the bootstrap cycle. The same bytecode artifact then
became the production parser used by the compiler, formatter, analysis, LSP,
embedding, and TalkSwift.

That production choice is now the dominant editor cost. The syntax workspace
executes roughly 214 million VM instructions per frontend corpus pass. In the
LSP latency workload, parsing `Parser.tlk` and rebuilding its workspace spend
nearly all CPU time in the VM interpreter. The existing C backend already
translates the complete finalized MIR vocabulary and its generated native code
is substantially faster than interpreted bytecode.

The obstacle is artifact shape, not language coverage. `talk-c` and
`talk-llvm` only emit executables: they synthesize `main`, keep language
functions private, and ignore `Module.exports` at the native boundary. Although
the compiler can publish named MIR exports, neither native backend can produce
a linkable library exposing them.

The embedding boundary is a separate concern. Swift requires a C-compatible
interface to the Rust compiler, which is owned by `talk-ffi`. Moving that code
into the compiler crate would reduce the crate count but would not remove the
FFI boundary. Conversely, making `talk-ffi` choose or manage a frontend would
put compiler policy in the wrong owner.

## Decision

### 1. There is one production source frontend

The canonical frontend remains the Talk source set in `stdlib/syntax`. Its
native artifact is the only production execution path for source parsing.
Compiler, formatter, analysis, LSP, REPL parsing, `talk-ffi`, and TalkSwift all
reach that same native implementation through `talk::compiling::frontend`.

There is no frontend provider, runtime strategy enum, Cargo feature selecting a
frontend, or VM fallback. Debug and release builds use the same native
frontend. A target that cannot build and link the native artifact is unsupported
and fails its build explicitly.

This is one frontend in both semantic ownership and production execution. C is
the compilation route for the frontend artifact; LLVM library emission exists
for backend parity and general library use, not as a second selectable
frontend.

### 2. Bytecode is a bootstrap seed, not a production frontend

`bootstrap/frontend.tbc` remains checked in because a parser is required to
compile the parser's own Talk sources. It is used only by explicit bootstrap
regeneration, fixed-point verification, and focused VM/differential tests.
Normal compiler and embedding execution do not load or execute it.

Bootstrap produces four tied artifacts from one fixed point:

- `bootstrap/frontend.tbc`, the next bootstrap seed;
- `bootstrap/frontend.abi`, the schema descriptor;
- `bootstrap/frontend.c`, the production frontend translation unit; and
- `bootstrap/frontend.manifest`, which hashes the sources and all generated
  artifacts.

Stage 1 parses with the checked-in seed. Stage 2 parses with the stage-1
candidate bytecode. The two stages must produce identical bytecode, ABI, and C
output. The native artifact therefore comes from the same verified frontend
program as the next seed; it is not an independently maintained implementation.

Ordinary builds never regenerate these files implicitly. They validate the
manifest, compile the checked-in C for the Cargo target, and link the resulting
object. Editing frontend sources without running bootstrap remains a hard
staleness failure.

### 3. C and LLVM can emit libraries from MIR exports

Both native backends gain an explicit library artifact mode alongside their
existing executable mode.

Executable mode remains unchanged: it requires a nullary entry, emits `main`,
and renders the result as a process.

Library mode:

- consumes `Module.exports` as the authoritative export list;
- emits no `main` and does not invoke the inert MIR entry;
- keeps implementation functions and dispatch machinery private;
- emits one externally visible wrapper for each named MIR export;
- accepts a caller-supplied symbol prefix so multiple generated libraries can
  coexist;
- uses deterministic collision-free mangling for arbitrary UTF-8 Talk names;
- emits a matching C header and an export-name-to-symbol manifest; and
- reports malformed export ids, duplicate external symbols, or invalid prefixes
  as adapter errors.

C and LLVM wrappers expose the same versioned C-compatible call convention: an
output slot, a contiguous argument array, and an argument count. The wrapper
checks arity before entering generated Talk code. Values use the native
runtime's uniform boundary representation; backend-private native signatures
remain behind the wrapper.

Library artifacts also expose namespaced initialization and teardown entry
points. A successful result remains valid until teardown. The initial contract
allows one active invocation per generated library and is not reentrant; the
owner must serialize calls. This states the current native runtime's global
state honestly rather than claiming context isolation it does not implement.

A native library boundary may not terminate its host. Talk traps and native
runtime failures are contained by the invocation boundary, returned as an
error status, and followed by complete invocation cleanup. No C or Rust unwind
crosses the boundary. Executable mode retains its current process-exit
semantics.

### 4. The compiler owns native frontend invocation

`talk::compiling::frontend` owns the private binding to the generated frontend
library. Its public Rust parsing functions remain the canonical API; analysis,
LSP, formatter, and embedding callers do not know that generated C is involved.

The existing ABI descriptor remains the trust seam. Native results are checked
for record identity, variant tag, field and payload shape, array bounds, spans,
and node identities before becoming compiler-private AST values. The bridge may
share representation-neutral validation machinery with bootstrap's bytecode
checks, but there is no production backend choice in that machinery.

Native calls are serialized inside the frontend owner until the native runtime
supports isolated invocation contexts. Validation and adaptation complete
before teardown invalidates the native result.

### 5. `talk-ffi` remains only the language-neutral host boundary

`talk-ffi` does not select, initialize, or directly bridge the native frontend.
It continues to call the public compiler and analysis APIs from `talk`, and
therefore uses the sole native frontend transitively.

Its public header, status model, opaque handles, ownership rules, panic
containment, callback rules, and exported symbol set do not change. Generated
frontend symbols are private implementation symbols and must not appear in the
`talk-ffi` ABI oracle.

TalkSwift continues to consume `talk-ffi`. Host static libraries and every
architecture in `TalkFFI.xcframework` include the native frontend object, so
existing Swift diagnostics, formatting, completion, navigation, and package
APIs gain the native frontend without public Swift changes.

Bytecode remains valid for dynamic program execution, package run/test, the
REPL evaluator, procedural macros, wasm program execution, and VM tests. Those
uses do not make bytecode an alternate source frontend.

## Implementation sequence

1. Add explicit executable and library emission APIs to `talk-c`; make the
   existing C CLI export options produce a real library artifact.
2. Add equivalent library emission and export options to `talk-llvm`, including
   namespaced LLVM-to-runtime bridge symbols.
3. Pin the shared native library call convention, lifecycle, trap containment,
   and generated header with C harness tests against both backends.
4. Extend bootstrap to retain the fixed-point MIR long enough to emit
   `frontend.c`, compare stage outputs, and include it in the manifest.
5. Compile and link `frontend.c` for every supported target as part of the
   normal `talk` build.
6. Replace production `run_export` calls in `compiling::frontend` with the
   direct native binding, retaining bytecode execution only in bootstrap and
   differential tests.
7. Rebuild `talk-ffi` and the TalkSwift XCFramework without changing their
   public interfaces.
8. Remove production frontend-selection and fallback code, then update ADR 0043
   implementation notes and frontend documentation to name native execution as
   authoritative.

Each stage lands with its own tests; the frontend is not switched until native
error containment, result validation, and target builds are complete.

## Acceptance criteria

- C and LLVM library artifacts expose every `Module.exports` entry and contain
  no `main`.
- Two generated libraries with distinct prefixes link into one process without
  symbol collisions.
- C and LLVM callers use the same generated header-level call convention and
  agree with VM results on exported scalar, String, aggregate, effect, and
  failure cases.
- `talk bootstrap --check` verifies source, bytecode, ABI, and C artifacts at a
  fixed point.
- No normal compiler, formatter, analysis, LSP, `talk-ffi`, or TalkSwift path
  executes `bootstrap/frontend.tbc`.
- Native and bootstrap-bytecode frontend results agree over the parser corpus,
  including malformed and lenient inputs.
- Native frontend traps return compiler errors and never exit an embedding
  host.
- Existing `talk-ffi` C smoke tests and exported-symbol oracle pass unchanged.
- TalkSwift host tests and every XCFramework target build pass unchanged.
- Editor latency is remeasured against the benchmark corpus after the cutover;
  correctness gates do not depend on a particular speedup.

## Consequences

- Building Talk now requires a target C compiler even when the user does not
  request C output. This is a deliberate requirement of shipping one native
  frontend.
- Cross-target and wasm builds must compile the generated frontend C for their
  target. Unsupported toolchains fail rather than changing frontend behavior.
- Clean builds gain the cost of compiling the generated frontend translation
  unit. Cargo caching avoids repeating that work while its source and target
  configuration are unchanged.
- The checked-in native C file is large generated bootstrap material, but it is
  reproducible, manifest-bound, and never manually edited.
- The VM remains important, but frontend VM optimization is no longer the route
  to production editor latency.
- `talk-ffi` remains a necessary Swift/Rust language boundary without becoming
  a frontend policy layer.
- No third-party dependency is required by this decision.
