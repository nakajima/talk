# 0066 - Retire the LLVM backend

Status: accepted (removed 2026-08-15)

## Context

The LLVM backend mirrored the C emitter arm for arm, emitting textual IR
against a thin pointer-ABI shim over the same native runtime. It earned
its keep while it was a second, independent check on lowering — but
every feature since has meant implementing each backend twice for one
target audience, and ADR 0065's resumable-function lowering was about to
double the largest emitter change yet. The C backend is the native
story: it produces the shipped artifacts, carries the exit-time leak
accounting the corpus leans on, and clang compiles its output through
LLVM anyway.

## Decision

Delete the `talk-llvm` crate. The C backend is the sole native target;
the VM remains the reference and the wasm story. Suspension (ADR 0065)
lands native on C only, and the "LLVM seam rejection" contingency in
ADR 0064/0065 is moot.

## Consequences

- One native lowering to write, test, and keep honest per feature; the
  parity story is VM ↔ C.
- The corpus sweeps lose one redundant lane; nothing else consumed the
  crate (no CLI command, no CI job, no library dependency).
- Reviving an LLVM (or Cranelift) backend later starts from the MIR
  contract in `docs/` and the C emitter as the model, not from the
  deleted code.
