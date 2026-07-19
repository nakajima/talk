# Commit 052: `79086d6e` - typed-program: reject monomorphic instantiation mappings

| Field | Value |
|---|---|
| Commit | `79086d6e1cf6e8b8d46d43f2f9a357232586895b` |
| Parent reviewed | `d35531541622298c6bbd9b5e921f8050c2e59b7f` |
| Author date | 2026-07-15T16:48:43-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +115 / -13 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 3.
- Production Rust: 1 files (+110/-11): `src/compiling/typed_program/contract.rs`.
- Documentation and plans: 2 files (+5/-2): `docs/backend-parity-ledger.md`, `docs/backend-status.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 110 | 11 |
| `docs/backend-status.md` | 4 | 1 |
| `docs/backend-parity-ledger.md` | 1 | 1 |

### Representative declarations touched

- `impl TypedProgramValidator<'_> {`
- `fn callable_function_instantiation`
- `fn monomorphic_instantiation_program`
- `fn monomorphic_instantiation_mut`
- `fn validator_rejects_unexpected_monomorphic_instantiation_mapping`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (3s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (17s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `validator_rejects_unexpected_monomorphic_instantiation_mapping`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
