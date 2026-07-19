# Commit 057: `535678c8` - mir: tighten provenance relevance checks

| Field | Value |
|---|---|
| Commit | `535678c8e525b0af5e6a4bd41f288c56d3254128` |
| Parent reviewed | `bdbcb1a335034c9cbb746eae8447bc0977941cb9` |
| Author date | 2026-07-15T17:23:51-07:00 |
| Author | Pat Nakajima |
| Patch size | 5 files, +228 / -31 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 5.
- Production Rust: 5 files (+228/-31): `src/mir/provenance.rs`, `src/mir/provenance/context.rs`, `src/mir/provenance/fixture_context.rs`, `src/mir/provenance/fixtures.rs`, `src/mir/provenance/tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/provenance/tests.rs` | 99 | 0 |
| `src/mir/provenance/context.rs` | 53 | 18 |
| `src/mir/provenance.rs` | 58 | 10 |
| `src/mir/provenance/fixtures.rs` | 16 | 1 |
| `src/mir/provenance/fixture_context.rs` | 2 | 2 |

### Representative declarations touched

- `impl OwnershipDiagnostic {`
- `fn non_borrow_event_is_relevant`
- `impl<'graph, 'mir> ProvenanceVerifier<'graph, 'mir> {`
- `impl<'mir> BorrowProvenanceContext<'mir> {`
- `fn capture_target`
- `impl FixtureContext {`
- `pub(crate) fn mutable_conflict() -> (ProvenanceFixture, OwnershipDiagnostic) {`
- `fn closure_and_handler_captures_reach_concrete_incoming_loans() {`
- `fn capture_transition_requires_the_construction_target_callable`
- `fn direct_projection_requires_the_newly_defined_loan_subject`
- `fn mutable_conflict_publishes_complete_diagnostic_subgraph() {`
- `fn move_in_terminator_is_structurally_valid() {`
- `fn non_borrow_diagnostic_rejects_focus_inflation_across_components`
- `fn non_borrow_diagnostic_allows_an_empty_focus_with_relevant_owner_cause`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (16s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `capture_transition_requires_the_construction_target_callable`, `direct_projection_requires_the_newly_defined_loan_subject`, `non_borrow_diagnostic_rejects_focus_inflation_across_components`, `non_borrow_diagnostic_allows_an_empty_focus_with_relevant_owner_cause`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
