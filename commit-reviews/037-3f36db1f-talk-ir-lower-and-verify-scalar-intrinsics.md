# Commit 037: `3f36db1f` - talk-ir: lower and verify scalar intrinsics

| Field | Value |
|---|---|
| Commit | `3f36db1fa057ba772bdc244f853071fca3160a28` |
| Parent reviewed | `b7dc18fb0cea89c64a2f73853e59a44b3667fd25` |
| Author date | 2026-07-15T00:19:20-07:00 |
| Author | Pat Nakajima |
| Patch size | 7 files, +249 / -46 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 7.
- Production Rust: 2 files (+201/-19): `src/talk_ir/lowering.rs`, `src/talk_ir/mod.rs`.
- Documentation and plans: 5 files (+48/-27): `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/talk_ir/lowering.rs` | 110 | 4 |
| `src/talk_ir/mod.rs` | 91 | 15 |
| `docs/backend-status.md` | 10 | 9 |
| `docs/backend-parity-ledger.md` | 10 | 9 |
| `docs/e1-scalar-execution-plan.md` | 13 | 5 |
| `docs/stage-0-contract-types.md` | 12 | 0 |
| `docs/backend-parity-plan.md` | 3 | 4 |

### Representative declarations touched

- `pub enum IrConstant {`
- `pub enum TalkIrInvariant {`
- `impl<'lowerer, 'mir> FunctionLowerer<'lowerer, 'mir> {`
- `fn preserves_scalar_intrinsics_from_typed_program_through_talk_ir`
- `impl<'ir> TalkIrVerifier<'ir> {`
- `fn scalar_ir_type`
- `fn scalar_intrinsic_candidate`
- `fn verifier_checks_scalar_intrinsic_signatures`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (17s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `preserves_scalar_intrinsics_from_typed_program_through_talk_ir`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
