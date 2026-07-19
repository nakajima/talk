# Commit 012: `761a7994` - close callable copy and ownership contract gaps

| Field | Value |
|---|---|
| Commit | `761a79940201fd484a57273d1bb1b9b1d3dbbe60` |
| Parent reviewed | `4c5413215496a7e3f050c29b1367bb3d2aed4fbb` |
| Author date | 2026-07-14T10:01:40-07:00 |
| Author | Pat Nakajima |
| Patch size | 10 files, +1526 / -384 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 10.
- Production Rust: 7 files (+1189/-229): `src/compiling/contracts.rs`, `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`, `src/talk_ir/lowering.rs`, `src/talk_ir/mod.rs`.
- Documentation and plans: 3 files (+337/-155): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/mod.rs` | 312 | 34 |
| `src/compiling/contracts.rs` | 312 | 7 |
| `src/compiling/typed_program/contract.rs` | 246 | 54 |
| `src/mir/verify.rs` | 171 | 63 |
| `docs/stage-0-contract-types.md` | 179 | 47 |
| `src/mir/generate.rs` | 123 | 67 |
| `docs/backend-status.md` | 85 | 96 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 73 | 12 |
| `src/talk_ir/lowering.rs` | 23 | 3 |
| `src/talk_ir/mod.rs` | 2 | 1 |

### Representative declarations touched

- `pub enum Mutability {`
- `enum CopyEvidence`
- `pub enum UseMode {`
- `pub enum PassingMode {`
- `pub enum CaptureMode {`
- `struct ExternalCallable`
- `enum ExternalCallableAvailability`
- `pub enum OriginRole {`
- `pub struct TypedFunction {`
- `enum TypedFunctionImplementation`
- `pub enum FunctionRole {`
- `pub struct TypedGlobal {`
- `pub enum TypedProgramInvariant {`
- `pub struct MirItem {`
- `pub enum MirItemKind {`
- `struct MirCallable`
- `enum MirCallableImplementation`
- `pub struct MirRequirement {`
- ...and 57 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (12s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `copy_evidence_proves_bounds_conformances_and_phantom_enums`, `rejects_copy_evidence_that_does_not_prove_the_used_type`, `preserves_bodyless_external_callable_contracts`, `ownership_diagnostic_derives_related_origins_from_non_focus_events`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
