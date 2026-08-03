# Documentation map

This directory contains current design documentation and architectural decision
records. Implementation plans are removed after completion; Git history is the
archive. Executable behavior is authoritative only when backed by the current
code and tests.

## Current documents

- [Backend crate extraction plan](backend-crate-extraction-plan.md) - staged
  migration to public MIR and separate bytecode, VM, C, LLVM, native-runtime,
  FFI, and Swift modules. Implemented by ADR 0047.
- [Backend extraction baseline](backend-extraction-baseline.md) - stage 0
  measurements, the ABI symbol oracle, and final post-extraction accounting.
- [Ownership](ownership.md) - implicit-sharing semantics and MIR ownership
  dataflow.
- [Effects](effects.md) - generic effect rows, handlers, and effect parameters
  carried by nominal types.
- [Panic audit](panic-audit.md) - LSP panic-containment policy and explicit
  production allowances.
- [Protocol arguments versus associated types](protocol-arguments-vs-associated-types.md)
  - explanatory type-system rationale.

## Historical evidence

These documents are snapshots rather than current project plans:

- [Backend parity ledger](backend-parity-ledger.md) - completed restoration
  accounting for the frontend-only reset.
- [Backend unsupported inventory](backend-unsupported-inventory.md) - ADR 0037's
  original line-numbered planning inventory.
- [Profiling findings](profiling-findings.md) - performance snapshots with their
  measured commits and workloads.
- [Self-hosted frontend VM report](frontend-vm-report.md) - optimization snapshot
  at commit `0b633a91`.
- [R1 managed-storage contract sketch](r1-managed-storage-contract-sketch.md) -
  the ADR 0033 sketch now consolidated by proposed ADR 0044.

Historical evidence must name the commit or date it describes and must not call
itself current.

## ADRs

An ADR records why a decision was made. Accepted, rejected, and superseded ADRs
remain in the tree. After acceptance, only status, implementation notes, and
supersession metadata should change; a semantic change requires a new ADR.

Status vocabulary:

- **Proposed** - awaiting a decision.
- **Accepted** - the decision is binding.
- **Implemented** - the accepted decision is present in production code.
- **Partially implemented** - accepted, with named implementation work open.
- **Rejected** - considered and deliberately not adopted.
- **Superseded** - retained as history; a later ADR is authoritative.

### Open or partially implemented

- [0007 - Checker responsibility extraction](adr/0007-checker-responsibility-extraction.md)
- [0020 - Axiom schemes and evidence](adr/0020-axiom-schemes-and-evidence.md)
- [0022 - Syntax sugars](adr/0022-sugar.md)
- [0026 - Hygienic syntax macros](adr/0026-macros.md)
- [0033 - Managed storage, heap regions, and FFI lifetimes](adr/0033-managed-storage-heap-regions-and-ffi-lifetimes.md)
- [0036 - Canonical instance heads](adr/0036-canonical-instance-heads-for-extensions.md)
- [0037 - Eliminate backend capability rejections](adr/0037-eliminate-backend-unsupported-behavior.md)
- [0044 - Unified memory model](adr/0044-the-unified-memory-model.md)

### Current implemented decisions

- [0001 - Qualified predicates](adr/0001-qualified-predicates.md)
- [0002 - GADT prerequisites](adr/0002-gadts-outsidein-existentials.md)
- [0003 - Protocol existentials](adr/0003-first-class-protocol-existentials.md)
- [0004 - Solver decomposition](adr/0004-solver-module-decomposition.md)
- [0005 - Type traversal primitives](adr/0005-type-traversal-primitives.md)
- [0012 - Unicode character model](adr/0012-unicode-character-model.md)
- [0013 - Sequential local scoping](adr/0013-sequential-scoping-for-locals.md)
- [0014 - Comparisons borrow operands](adr/0014-comparisons-borrow-their-operands.md)
- [0016 - Protocol arguments in conformance identity](adr/0016-protocol-argument-conformance-keys.md)
- [0018 - Borrow-by-default parameters](adr/0018-borrow-by-default-parameters.md)
- [0021 - First-class iteration](adr/0021-first-class-iteration-and-borrow-default-for-loops.md)
- [0023 - Packages](adr/0023-packages.md)
- [0024 - Labeled enum payloads](adr/0024-named-enum-values.md)
- [0025 - Borrow-transparent patterns](adr/0025-borrow-transparent-pattern-occurrences.md)
- [0028 - Structured diagnostics](adr/0028-structured-diagnostics-and-conservative-code-actions.md)
- [0031 - Frontend-only reset](adr/0031-frontend-only-backend-reset.md)
- [0034 - Lean bytecode backend](adr/0034-lean-bytecode-backend-architecture.md)
- [0035 - Static value generics](adr/0035-static-value-generics.md)
- [0038 - MIR semantic-authority cleanup](adr/0038-mir-cleanup.md)
- [0039 - Host fallback handlers](adr/0039-typed-ambient-effects-and-host-fallback.md)
- [0041 - Callable argument labels](adr/0041-callable-argument-labels.md)
- [0042 - Symbol visibility](adr/0042-symbol-visibility-and-public-module-interfaces.md)
- [0043 - Self-hosted source frontend](adr/0043-self-hosted-source-frontend.md)

### Historical, superseded, or rejected

- [0006 - Constraint generator decomposition](adr/0006-checker-module-decomposition.md)
- [0008 - Managed storage and FFI source direction](adr/0008-managed-storage-and-ffi.md)
- [0009 - Standalone executables](adr/0009-standalone-executables-via-bundled-vm.md)
- [0010 - Flow analysis on MIR](adr/0010-flow-analysis-on-the-mir-cfg.md)
- [0011 - Dynamic-extent effect handlers](adr/0011-dynamic-extent-effect-handlers.md)
- [0015 - Typing publishes, lowering reads](adr/0015-typing-publishes-lowering-reads.md)
- [0017 - Structural temporary drops](adr/0017-structural-temp-drops-and-free-balance-verifier.md)
- [0019 - TypedProgram to CheckedMir](adr/0019-typed-program-to-checked-mir.md)
- [0027 - Effect abort unwinding](adr/0027-effect-abort-unwinding.md)
- [0029 - Uniform RC baseline](adr/0029-uniform-rc-baseline.md)
- [0030 - Structural drop-candidate claiming](adr/0030-structural-drop-candidate-claiming.md)
- [0032 - Single-artifact lowering pipeline](adr/0032-single-artifact-ownership-and-lowering-pipeline.md)
- [0040 - Frame-or-region closure environments](adr/0040-frame-or-region-closure-environments.md)

## Module documentation

Current implementation structure is documented next to the code:

- [`src/compiling`](../src/compiling/README.md)
- [`src/types`](../src/types/README.md)
- [`src/name_resolution`](../src/name_resolution/README.md)
- [`src/parsing`](../src/parsing/README.md)
- [`src/desugar`](../src/desugar/README.md)
- [`src/analysis`](../src/analysis/README.md)
- [`src/lsp`](../src/lsp/README.md)
- [`src/cli`](../src/cli/README.md)

## Maintenance rules

1. Put durable decisions in ADRs, not project plans.
2. Remove completed plans after extracting lasting decisions and updating
   references.
3. Mark reports and audits with their commit or verification date.
4. Keep one owner for each current semantic rule; historical documents must
   point to that owner rather than restating current status.
5. Update links and source comments in the same change that moves a document.
