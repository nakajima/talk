# Commit 025: `4f890f2c` - enforce semantic occurrence completeness

| Field | Value |
|---|---|
| Commit | `4f890f2cad11442a2cce079a9387190e3d170a6d` |
| Parent reviewed | `a364a34b7b37387981f72f9c26a2330c5ae65c32` |
| Author date | 2026-07-14T17:31:44-07:00 |
| Author | Pat Nakajima |
| Patch size | 5 files, +486 / -78 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 5.
- Production Rust: 2 files (+455/-62): `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`.
- Documentation and plans: 3 files (+31/-16): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 357 | 16 |
| `src/compiling/typed_program/build.rs` | 98 | 46 |
| `docs/stage-0-contract-types.md` | 11 | 6 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 10 | 7 |
| `docs/backend-status.md` | 10 | 3 |

### Representative declarations touched

- `pub struct TypedProgram {`
- `impl TypedTreeBuilder<'_> {`
- `fn source_selection_span`
- `pub(crate) fn build_program(`
- `impl<'a> SourceOccurrenceCollector<'a> {`
- `impl SemanticOccurrence {`
- `fn record_in`
- `impl TypedProgram {`
- `impl ModuleInterface {`
- `pub enum TypedProgramInvariant {`
- `impl TypedProgramValidator<'_> {`
- `fn source_backed`
- `fn has_occurrence`
- `fn require_occurrence`
- `fn validate_semantic_occurrence_completeness`
- `fn semantic_occurrence_recording_deduplicates_only_identical_facts`
- `fn validator_rejects_missing_source_definition_occurrence`
- `fn validator_rejects_missing_canonical_resolution_occurrence`
- ...and 1 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (3s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (13s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `semantic_occurrence_recording_deduplicates_only_identical_facts`, `validator_rejects_missing_source_definition_occurrence`, `validator_rejects_missing_canonical_resolution_occurrence`, `validator_rejects_detached_semantic_occurrence_selection`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
