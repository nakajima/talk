# Commit 027: `03128941` - validate exact initializer ownership

| Field | Value |
|---|---|
| Commit | `031289412cfcef2b795d20357a5c09db70e63dd3` |
| Parent reviewed | `d84fe5892f2989a291c4e338c5610da67ed2d4a3` |
| Author date | 2026-07-14T20:20:14-07:00 |
| Author | Pat Nakajima |
| Patch size | 5 files, +215 / -28 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 5.
- Production Rust: 2 files (+192/-14): `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`.
- Documentation and plans: 3 files (+23/-14): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 179 | 13 |
| `docs/stage-0-contract-types.md` | 9 | 6 |
| `src/compiling/typed_program/build.rs` | 13 | 1 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 7 | 5 |
| `docs/backend-status.md` | 7 | 3 |

### Representative declarations touched

- `struct occurrence`
- `impl<'a> CanonicalBuilder<'a> {`
- `impl TypedProgram {`
- `pub enum TypedProgramInvariant {`
- `struct TypedProgramValidator<'program> {`
- `impl TypedProgramValidator<'_> {`
- `fn validate_initializer_ownership`
- `fn validator_rejects_initializer_owned_by_multiple_structs`
- `fn validator_rejects_ownerless_initializer`
- `fn validator_rejects_wrong_role_struct_initializer_entry`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (3s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (11s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `validator_rejects_initializer_owned_by_multiple_structs`, `validator_rejects_ownerless_initializer`, `validator_rejects_wrong_role_struct_initializer_entry`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
