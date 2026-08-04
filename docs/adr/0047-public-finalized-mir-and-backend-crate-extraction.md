# ADR 0047: Public finalized MIR and backend crate extraction

Status: accepted

ADR 0048 subsequently amends the frontend-specific parts of sections 2 and 5:
C and LLVM gain native library artifacts, and the source frontend executes
natively in production. `talk-ffi` remains the language-neutral host boundary.

Amends the implementation-shape decisions of ADR 0034. The trust policy
(ADR 0034 section 3), the provenance policy, and the size-accounting
discipline remain in force. Execution plan:
[Backend crate extraction plan](../backend-crate-extraction-plan.md).
Baseline measurements: [backend extraction baseline](../backend-extraction-baseline.md).

## Context

ADR 0034 kept the whole backend private inside the compiler crate on an
explicit condition: "There is no separate public target-neutral IR module
unless a second real target adapter requires one." That condition has now
been met three times over. The C emitter (`src/backend/c.rs`), the bytecode
lowerer (`src/backend/lower.rs`), and the external LLVM backend
(`talk-llvm`) are three real adapters consuming the same finalized MIR, and
the LLVM adapter already forced a public duplicate: `src/codegen.rs`
re-declares the MIR vocabulary and `src/backend/codegen.rs` projects into it
exhaustively, so every MIR change is paid for twice.

ADR 0034 also named bytecode "the only parity backend" with `talk run`,
packages, tests, the REPL, standalone executables, embedding, and the
browser all calling one `compile`/`execute` pair. That remains true at the
behavior level, but the private seam now costs more than it hides:

- The C backend needs frame-shaping facts (ADR 0045 escape summaries and
  frame sites) that the bytecode path never computes, so `src/backend/mod.rs`
  carries a C-only prepass (`parameter_summaries` before register
  allocation, `shape_frames` after). There is no single finalized form a
  target can consume; each entry point re-runs a slightly different
  pipeline.
- The compiler crate owns the VM's executable wrapper, target pools, and
  instruction fusion, so VM-adjacent changes rebuild the compiler and
  compiler changes force VM-adjacent review.
- The embedding crate is named `talk-c` while a C code generator also
  exists, and the two are routinely confused. The embedding interface is
  language-neutral (its Swift consumer is one binding), so the name is wrong
  on both axes.

## Decision

### 1. Finalized MIR is the public target seam

The compiler publishes one finalized, target-independent MIR module per
compilation. C, bytecode, and LLVM adapters consume exactly that module and
nothing else: no `TypedProgram`, type catalog, parser node, source span, or
name-resolution query. There is no separate public `codegen` representation;
`src/codegen.rs` and its projection are deleted. There is no backend trait
or registry; each real adapter matches the public MIR exhaustively.

The single publication path runs, in order: MIR construction and ownership
checking, optimization, pre-allocation parameter escape summaries, register
allocation, and frame stamping under final numbering. The C-only prepass in
`src/backend/mod.rs` disappears into that path, so no target needs a
compiler-private variant of the pipeline.

### 2. Bytecode remains the parity target, split into adapter and VM

Bytecode is still the parity execution target and still backs every current
dynamic surface (`talk run`, packages, tests, REPL, embedding, wasm, the
self-hosted frontend). It is no longer private compiler implementation:

- `talk-bytecode` owns MIR-to-bytecode lowering, target pools,
  linearization, fusion, and the executable wrapper. It depends on the
  public MIR and the VM, never on the compiler.
- `talk-vm` (renamed from `talk-runtime`) owns the bytecode format,
  encoding, validation, interpreter, memory, objects, host IO, budgets, and
  statistics. It does not know MIR exists.

The two VM trust paths stay distinct: the adapter constructs in-memory
modules under compiler invariants, while decoded byte images remain
untrusted and validate before execution (ADR 0034 section 3, unchanged).

### 3. In-process MIR stays trusted and unserialized

The public module is trusted in-process data. This ADR does not add MIR
serialization, a compatibility version, serialization-grade validation, or a
fixture-only builder framework. Construction invariants, focused assertions,
and black-box source fixtures remain the semantic oracle, exactly as ADR
0034 section 3 prescribes for values produced and consumed inside one
compiler invocation. Adapters return target errors for malformed manually
constructed modules; they do not replay source semantics.

### 4. Native backends share one C runtime

C and LLVM consume one native C runtime source owned by a small first-party
`talk-native-runtime` crate. Neither backend depends on the other to obtain
it. The LLVM pointer-ABI bridge (`talk-llvm/src/llvm_runtime.c`) stays
LLVM-owned.

### 5. The embedding interface is language-neutral `talk-ffi`

The current `talk-c` embedding package is renamed `talk-ffi`, preserving
every exported `talk_*` function, result layout, and ownership contract.
TalkSwift is one binding over that interface, not its owner, and keeps its
public Swift declarations unchanged. `talk-ffi` remains VM-backed: source
execution composes `compile_mir`, `talk_bytecode::compile`, and
`talk_vm::execute`. The freed `talk-c` package name is reused for the C
backend. A host-callable native ABI for compiled Talk programs is not part
of this decision.

### 6. What is amended

From ADR 0034 section 2: the absence of a public target-neutral IR module
was conditioned on a second real target adapter. Three exist; the condition
is met; the finalized MIR becomes the one public seam. The unoptimized MIR
used for ownership work and debugging stays private.

From ADR 0034 section 5: "C/Swift embedding ... call the same
compile/execute pair" is preserved behaviorally, but the pair is now a
composition across `talk`, `talk-bytecode`, and `talk-vm` rather than two
methods inside one crate.

Nothing else in ADR 0034 is amended. In particular: private phases remain
the default for anything with one consumer; a new seam still requires two
real consumers; the trust policy and the accounting discipline stand.

## Consequences

- Adding a MIR instruction or changing a layout contract breaks all three
  adapters at compile time through exhaustive matching; parity is enforced
  structurally instead of by ledger review alone.
- `talk-mir` cannot depend on the compiler, so source-level
  `name_resolution::Symbol` cannot appear in public MIR data. The compiler
  translates the three instruction positions that carry symbols
  (`PushHandler.effect`, `FindHandler.effect`, `ExistentialPack.protocol`)
  to a compact `MirSymbol` at emission; every other `Symbol` use in the MIR
  module is already builder-private.
- The compiler keeps its current conveniences (REPL, tests, bootstrap,
  procedural macros, self-hosted frontend) by depending on `talk-bytecode`
  and `talk-vm`; the dependency direction is one-way, so no cycle is
  possible.
- The `talk-runtime` -> `talk-vm` and `talk-c` -> `talk-ffi` renames touch
  Cargo manifests, Swift packaging, CI, and release workflows. They are
  performed as separate mechanical stages with their own oracles
  (byte-identical encoded fixtures for the VM rename; the exported symbol
  list for the FFI rename) so regressions are attributable.
- Bytecode wire format, the checked-in self-hosted frontend artifact, VM
  behavior and accounting, generated C and LLVM behavior, the C ABI symbol
  set, the TalkSwift public interface, and CLI spelling are all preserved;
  each stage names the oracle that proves it.
- No new third-party dependency is introduced.
