# Commit 036: `b7dc18fb` - mir: generate and verify scalar intrinsics

| Field | Value |
|---|---|
| Commit | `b7dc18fb0cea89c64a2f73853e59a44b3667fd25` |
| Parent reviewed | `bca268e70b9ba61c998464c3c3c89143b6dbe261` |
| Author date | 2026-07-15T00:08:07-07:00 |
| Author | Pat Nakajima |
| Patch size | 8 files, +484 / -76 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 8.
- Production Rust: 3 files (+438/-52): `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`.
- Documentation and plans: 5 files (+46/-24): `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/generate.rs` | 314 | 10 |
| `src/mir/mod.rs` | 76 | 39 |
| `src/mir/verify.rs` | 48 | 3 |
| `docs/backend-status.md` | 14 | 10 |
| `docs/backend-parity-ledger.md` | 8 | 10 |
| `docs/stage-0-contract-types.md` | 14 | 0 |
| `docs/e1-scalar-execution-plan.md` | 8 | 1 |
| `docs/backend-parity-plan.md` | 2 | 3 |

### Representative declarations touched

- `pub struct MirCaptureOperand {`
- `pub enum MirInvariant {`
- `impl<'program> FunctionGenerator<'program> {`
- `fn lower_scalar_inline_ir`
- `fn initialize_temporary`
- `fn generates_scalar_intrinsics_from_canonical_typed_operands`
- `fn rejects_deferred_inline_ir_before_partial_mir`
- `fn verifies_scalar_intrinsic_signatures`
- `impl<'mir> MirVerifier<'mir> {`
- `fn scalar_ty`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (3s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (16s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `generates_scalar_intrinsics_from_canonical_typed_operands`, `rejects_deferred_inline_ir_before_partial_mir`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
