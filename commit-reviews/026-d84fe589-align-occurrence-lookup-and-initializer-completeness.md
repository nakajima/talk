# Commit 026: `d84fe589` - align occurrence lookup and initializer completeness

| Field | Value |
|---|---|
| Commit | `d84fe5892f2989a291c4e338c5610da67ed2d4a3` |
| Parent reviewed | `4f890f2cad11442a2cce079a9387190e3d170a6d` |
| Author date | 2026-07-14T19:57:04-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +186 / -28 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 4.
- Production Rust: 1 files (+171/-21): `src/compiling/typed_program/contract.rs`.
- Documentation and plans: 3 files (+15/-7): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 171 | 21 |
| `docs/stage-0-contract-types.md` | 5 | 3 |
| `docs/backend-status.md` | 5 | 2 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 5 | 2 |

### Representative declarations touched

- `impl TypedProgram {`
- `impl TypedProgramValidator<'_> {`
- `fn target_lookup_treats_adjacent_selection_end_as_exclusive`
- `fn validator_requires_struct_occurrence_for_generated_and_declared_initializer_calls`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (9s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `target_lookup_treats_adjacent_selection_end_as_exclusive`, `validator_requires_struct_occurrence_for_generated_and_declared_initializer_calls`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
