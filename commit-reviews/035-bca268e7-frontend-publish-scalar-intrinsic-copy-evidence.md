# Commit 035: `bca268e7` - frontend: publish scalar intrinsic copy evidence

| Field | Value |
|---|---|
| Commit | `bca268e70b9ba61c998464c3c3c89143b6dbe261` |
| Parent reviewed | `e179fb705fad13b6b4faec42dc6042f285d71be4` |
| Author date | 2026-07-14T23:52:22-07:00 |
| Author | Pat Nakajima |
| Patch size | 11 files, +184 / -66 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 11.
- Production Rust: 6 files (+148/-47): `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/types/generate/artifacts.rs`, `src/types/generate/expr.rs`, `src/types/generate/mod.rs`, `src/types/output.rs`.
- Documentation and plans: 5 files (+36/-19): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 74 | 12 |
| `src/compiling/typed_program/build.rs` | 34 | 18 |
| `src/types/generate/expr.rs` | 26 | 13 |
| `docs/stage-0-contract-types.md` | 15 | 6 |
| `docs/e1-scalar-execution-plan.md` | 9 | 6 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 7 | 4 |
| `src/types/output.rs` | 9 | 1 |
| `src/types/generate/mod.rs` | 4 | 2 |
| `docs/backend-status.md` | 4 | 2 |
| `src/types/generate/artifacts.rs` | 1 | 1 |
| `docs/backend-parity-ledger.md` | 1 | 1 |

### Representative declarations touched

- `pub enum CheckedInlineIrOperation {`
- `impl<'a> CanonicalBuilder<'a> {`
- `impl fmt::Display for ScalarIntrinsicOperand {`
- `impl ScalarIntrinsicOperand {`
- `impl TypedProgramValidator<'_> {`
- `pub(super) struct TypeArtifacts {`
- `impl<'s, 'a> BodyChecker<'s, 'a> {`
- `pub enum MemberResolution {`
- `struct ScalarIntrinsicPlan`
- `pub struct TypeOutput {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (5s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (21s).
- `git diff --check` passed for this commit against its first parent.
- No test files or executable language test fixtures changed in this patch.
- Coverage note: production behavior changes without a directly changed test surface in this commit; confidence therefore comes from existing suites and later integration coverage.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
