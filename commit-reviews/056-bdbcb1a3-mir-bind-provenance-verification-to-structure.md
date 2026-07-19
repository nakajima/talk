# Commit 056: `bdbcb1a3` - mir: bind provenance verification to structure

| Field | Value |
|---|---|
| Commit | `bdbcb1a335034c9cbb746eae8447bc0977941cb9` |
| Parent reviewed | `ebf07ef71b93baf2bbba8cc9e7a52a853af61f6a` |
| Author date | 2026-07-15T13:14:04-07:00 |
| Author | Pat Nakajima |
| Patch size | 6 files, +2589 / -603 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 2, M: 4.
- Production Rust: 6 files (+2589/-603): `src/lsp/borrow_provenance.rs`, `src/mir/provenance.rs`, `src/mir/provenance/context.rs`, `src/mir/provenance/fixture_context.rs`, `src/mir/provenance/fixtures.rs`, `src/mir/provenance/tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/provenance/context.rs` | 952 | 0 |
| `src/mir/provenance/fixture_context.rs` | 672 | 0 |
| `src/mir/provenance/fixtures.rs` | 390 | 187 |
| `src/mir/provenance.rs` | 294 | 256 |
| `src/mir/provenance/tests.rs` | 239 | 150 |
| `src/lsp/borrow_provenance.rs` | 42 | 10 |

### Representative declarations touched

- `fn render_borrow_provenance`
- `fn renderer_rejects_a_result_with_malformed_focus`
- `pub(crate) enum BorrowProvenanceInvariant {`
- `impl BorrowEventKind {`
- `fn is_definition_at`
- `fn verify`
- `impl BorrowProvenance {`
- `fn connected_to`
- `fn verify_provenance`
- `impl OwnershipDiagnostic {`
- `struct ProvenanceVerifier`
- `struct ProvenanceVerifier<'graph> {`
- `fn new`
- `impl<'graph> ProvenanceVerifier<'graph> {`
- `fn verify_definitions`
- `struct BorrowProvenanceContext`
- `fn borrow_provenance_context`
- `fn generation`
- ...and 73 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (18s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `renderer_rejects_a_result_with_malformed_focus`, `verification_context_is_derived_from_checked_mir_structure`, `mutable_conflict_publishes_complete_diagnostic_subgraph`, `context_rejects_owner_from_a_different_borrowed_place`, `context_rejects_wrong_projection_identity`, `duplicate_loan_definitions_are_rejected`, `move_in_terminator_is_structurally_valid`, `diagnostic_rejects_appended_unrelated_provenance`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
