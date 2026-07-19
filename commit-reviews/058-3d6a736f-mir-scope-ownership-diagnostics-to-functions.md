# Commit 058: `3d6a736f` - mir: scope ownership diagnostics to functions

| Field | Value |
|---|---|
| Commit | `3d6a736f9e67d40a1c7eee245af5eac7d4ba3bcf` |
| Parent reviewed | `535678c8e525b0af5e6a4bd41f288c56d3254128` |
| Author date | 2026-07-15T17:38:23-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +101 / -14 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 4.
- Production Rust: 4 files (+101/-14): `src/mir/provenance.rs`, `src/mir/provenance/context.rs`, `src/mir/provenance/fixtures.rs`, `src/mir/provenance/tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/provenance.rs` | 32 | 9 |
| `src/mir/provenance/tests.rs` | 33 | 5 |
| `src/mir/provenance/context.rs` | 29 | 0 |
| `src/mir/provenance/fixtures.rs` | 7 | 0 |

### Representative declarations touched

- `pub(crate) enum BorrowProvenanceInvariant {`
- `fn function`
- `impl OwnershipDiagnostic {`
- `fn non_borrow_event_is_relevant`
- `pub(crate) struct BorrowProvenanceContext<'mir> {`
- `struct OwnershipDiagnosticContext`
- `fn provenance`
- `fn is_valid`
- `impl<'mir> BorrowProvenanceContext<'mir> {`
- `fn for_ownership_diagnostic`
- `impl ProvenanceFixture {`
- `fn diagnostic_context`
- `fn mutable_conflict_publishes_complete_diagnostic_subgraph() {`
- `fn non_borrow_diagnostic_rejects_focus_inflation_across_components() {`
- `fn non_borrow_diagnostic_allows_an_empty_focus_with_relevant_owner_cause() {`
- `fn non_borrow_diagnostic_rejects_same_local_id_from_another_function`
- `fn diagnostic_rejects_appended_unrelated_provenance() {`
- `fn malformed_endpoints_and_diagnostic_focus_are_rejected() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (18s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `non_borrow_diagnostic_rejects_same_local_id_from_another_function`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
