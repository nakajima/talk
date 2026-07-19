# Commit 033: `536e3efb` - compiler: add target-neutral scalar intrinsics

| Field | Value |
|---|---|
| Commit | `536e3efbdef3593c465bc6d93e730922a756fc50` |
| Parent reviewed | `f74b9ae62dfec188cef9b8c8fd7d9ca96ce87b59` |
| Author date | 2026-07-14T22:49:39-07:00 |
| Author | Pat Nakajima |
| Patch size | 9 files, +452 / -37 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 9.
- Production Rust: 3 files (+301/-9): `src/compiling/contracts.rs`, `src/mir/mod.rs`, `src/talk_ir/mod.rs`.
- Documentation and plans: 6 files (+151/-28): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/contracts.rs` | 221 | 1 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 73 | 0 |
| `docs/stage-0-contract-types.md` | 53 | 10 |
| `src/mir/mod.rs` | 49 | 4 |
| `src/talk_ir/mod.rs` | 31 | 4 |
| `docs/backend-status.md` | 13 | 6 |
| `docs/e1-scalar-execution-plan.md` | 7 | 8 |
| `docs/backend-parity-plan.md` | 3 | 2 |
| `docs/backend-parity-ledger.md` | 2 | 2 |

### Representative declarations touched

- `enum ScalarType`
- `enum ScalarComparison`
- `enum ScalarIntrinsic`
- `pub enum Mutability {`
- `struct ScalarIntrinsicSignature`
- `pub enum Rvalue {`
- `pub struct MirCaptureOperand {`
- `pub enum InstructionKind {`
- `pub enum IrConstant {`
- `fn fmt`
- `fn scalar_intrinsics_have_closed_signatures_and_stable_names`
- `fn rejects_cataloged_intrinsics_until_the_verified_subset_adopts_them`
- `fn unsupported_intrinsic_candidate`
- `fn verifier_rejects_cataloged_intrinsics_until_the_verified_subset_adopts_them`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (6s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (22s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `scalar_intrinsics_have_closed_signatures_and_stable_names`, `rejects_cataloged_intrinsics_until_the_verified_subset_adopts_them`, `verifier_rejects_cataloged_intrinsics_until_the_verified_subset_adopts_them`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
