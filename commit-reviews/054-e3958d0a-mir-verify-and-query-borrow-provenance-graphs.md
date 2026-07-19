# Commit 054: `e3958d0a` - mir: verify and query borrow provenance graphs

| Field | Value |
|---|---|
| Commit | `e3958d0a7711d9db882e927ae86e99c9b51f785c` |
| Parent reviewed | `fe6b86861a18a722902d147a3a8e1ba02677d806` |
| Author date | 2026-07-15T12:41:59-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +1330 / -0 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 3, M: 1.
- Production Rust: 4 files (+1330/-0): `src/mir/mod.rs`, `src/mir/provenance.rs`, `src/mir/provenance/fixtures.rs`, `src/mir/provenance/tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/provenance.rs` | 660 | 0 |
| `src/mir/provenance/fixtures.rs` | 363 | 0 |
| `src/mir/provenance/tests.rs` | 306 | 0 |
| `src/mir/mod.rs` | 1 | 0 |

### Representative declarations touched

- `enum BorrowProvenanceInvariant`
- `fn subject`
- `fn verify`
- `fn query`
- `fn verify_provenance`
- `struct ProvenanceVerifier`
- `fn new`
- `fn verify_event`
- `fn relation_is_valid`
- `fn verify_predecessors`
- `fn verify_subject_connectivity`
- `fn reaches_origin`
- `fn valid_type`
- `fn relation_rank`
- `struct ProvenanceFixture`
- `struct FixtureBuilder`
- `fn origin`
- `fn event`
- ...and 22 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (23s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `queries_direct_borrow_from_owner_through_end`, `projected_reborrow_keeps_parent_projection_and_both_ends`, `mutable_conflict_publishes_complete_diagnostic_subgraph`, `call_transfer_joins_concrete_loan_to_abstract_parameter`, `closure_and_handler_captures_use_the_same_structural_query`, `branch_specific_endings_are_all_in_the_query_result`, `query_excludes_unrelated_connected_components_and_is_deterministic`, `invalid_event_graphs_cannot_publish_query_results`, `subject_and_diagnostic_focus_must_agree_with_structural_events`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
