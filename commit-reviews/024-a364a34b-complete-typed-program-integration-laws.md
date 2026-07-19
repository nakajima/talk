# Commit 024: `a364a34b` - complete typed program integration laws

| Field | Value |
|---|---|
| Commit | `a364a34b7b37387981f72f9c26a2330c5ae65c32` |
| Parent reviewed | `1fb9946bf65df5740d23f7cbfa38662b432e1627` |
| Author date | 2026-07-14T16:30:05-07:00 |
| Author | Pat Nakajima |
| Patch size | 16 files, +1917 / -219 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 1, M: 15.
- Production Rust: 13 files (+1756/-181): `src/analysis/completion.rs`, `src/compiling/contracts.rs`, `src/compiling/typed_program.rs`, `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/compiling/typed_program/serde_test.rs`, `src/lsp/code_actions.rs`, `src/mir/generate.rs`, and 5 more.
- Documentation and plans: 3 files (+161/-38): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 613 | 41 |
| `src/compiling/typed_program/serde_test.rs` | 556 | 0 |
| `src/compiling/typed_program/build.rs` | 237 | 43 |
| `src/talk_ir/lowering.rs` | 136 | 0 |
| `src/mir/generate.rs` | 86 | 29 |
| `src/lsp/code_actions.rs` | 16 | 53 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 61 | 7 |
| `docs/stage-0-contract-types.md` | 56 | 10 |
| `docs/backend-status.md` | 44 | 21 |
| `src/talk_ir/mod.rs` | 30 | 1 |
| `src/mir/verify.rs` | 26 | 0 |
| `src/analysis/completion.rs` | 12 | 11 |
| `src/compiling/contracts.rs` | 17 | 0 |
| `src/mir/mod.rs` | 14 | 0 |
| `src/compiling/typed_program.rs` | 6 | 3 |

### Representative declarations touched

- `pub struct TypedProgram {`
- `enum SemanticTarget`
- `enum SemanticOccurrenceRole`
- `pub struct TypedFile {`
- `pub enum TypedFunctionImplementation {`
- `struct CallableSupplier`
- `pub enum TypedProgramInvariant {`
- `pub struct MirExport {`
- `fn conformance_requirement_completions(`
- `fn directly_in_extend_body(extend: &Decl, byte_offset: u32) -> bool {`
- `pub enum ItemId {`
- `fn callable_link_name`
- `pub(crate) fn build_program(`
- `struct SourceOccurrenceCollector<'a> {`
- `impl<'a> SourceOccurrenceCollector<'a> {`
- `fn target`
- `fn push_name`
- `fn push_effect`
- ...and 107 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (6s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (16s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `validator_rejects_semantic_occurrence_with_missing_target`, `validator_rejects_semantic_occurrence_that_disagrees_with_resolution`, `validator_rejects_duplicate_or_mismatched_semantic_definitions`, `validator_rejects_semantic_occurrence_without_source_origin`, `validator_rejects_ambiguous_semantic_selections`, `internal_callable_links_ignore_session_local_module_ids`, `module_interface_assigns_unique_internal_links_to_private_witnesses`, `module_interface_serialization_round_trip_preserves_callable_links`, `invalid_copy_capture_never_publishes_checked_mir`, `rejects_duplicate_callable_supplier_links`, `source_external_link_matches_interface_mir_and_talk_ir_supplier`, `verifier_rejects_duplicate_export_link_names`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
