# Commit 059: `7685abc5` - merge: integrate lane C borrow provenance

| Field | Value |
|---|---|
| Commit | `7685abc5c50fccd6a50c766eef6560c3d91c9a8f` |
| Parent reviewed | `0a968e6728264eaeaaa1bbbc8c5035dfbde3c33f` |
| Other parents | `3d6a736f9e67d40a1c7eee245af5eac7d4ba3bcf` |
| Author date | 2026-07-15T18:27:43-07:00 |
| Author | Pat Nakajima |
| Patch size | 8 files, +3818 / -0 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 6, M: 2.
- Production Rust: 8 files (+3818/-0): `src/lsp/borrow_provenance.rs`, `src/lsp/mod.rs`, `src/mir/mod.rs`, `src/mir/provenance.rs`, `src/mir/provenance/context.rs`, `src/mir/provenance/fixture_context.rs`, `src/mir/provenance/fixtures.rs`, `src/mir/provenance/tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/provenance/context.rs` | 1016 | 0 |
| `src/mir/provenance.rs` | 769 | 0 |
| `src/mir/provenance/fixture_context.rs` | 672 | 0 |
| `src/mir/provenance/fixtures.rs` | 588 | 0 |
| `src/mir/provenance/tests.rs` | 522 | 0 |
| `src/lsp/borrow_provenance.rs` | 249 | 0 |
| `src/mir/mod.rs` | 1 | 0 |
| `src/lsp/mod.rs` | 1 | 0 |

### Representative declarations touched

- `fn render_borrow_provenance`
- `struct BorrowProvenanceRenderer`
- `fn new`
- `fn render`
- `fn event`
- `fn subject`
- `fn permission`
- `fn conflict`
- `fn markdown`
- `fn renders_verified_owner_to_use_query_as_lsp_markdown`
- `fn renderer_rejects_a_result_with_malformed_focus`
- `fn renders_reborrow_transfer_capture_endings_and_conflict`
- `enum BorrowProvenanceInvariant`
- `fn function`
- `fn is_definition_at`
- `fn verify`
- `fn query`
- `fn connected_to`
- ...and 89 additional declaration contexts.

## Test and validation review

- Historical checkout compilation was not repeated because this patch changes only documentation/language fixtures/oracles and no Rust or Cargo inputs.
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (17s): `compiling::package::tests::package_build_fails_closed_for_unsupported_source_forms`.
- This test failure is inherited from `0a968e67`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `renders_verified_owner_to_use_query_as_lsp_markdown`, `renderer_rejects_a_result_with_malformed_focus`, `renders_reborrow_transfer_capture_endings_and_conflict`, `verification_context_is_derived_from_checked_mir_structure`, `queries_direct_borrow_from_owner_through_end`, `projected_reborrow_agrees_with_canonical_field_and_place_type`, `call_transfer_joins_abstract_parameter_to_callee_incoming_loan`, `closure_and_handler_captures_reach_concrete_incoming_loans`, `capture_transition_requires_the_construction_target_callable`, `direct_projection_requires_the_newly_defined_loan_subject`, `mutable_conflict_publishes_complete_diagnostic_subgraph`, `branch_specific_endings_are_all_in_the_query_result`, `query_excludes_unrelated_components_and_remaps_edges_deterministically`, `context_rejects_nonexistent_locations_and_out_of_range_origins`, `context_rejects_owner_from_a_different_borrowed_place`, `context_rejects_wrong_projection_identity`, `duplicate_loan_definitions_are_rejected`, `move_in_terminator_is_structurally_valid`, `non_borrow_diagnostic_rejects_focus_inflation_across_components`, `non_borrow_diagnostic_allows_an_empty_focus_with_relevant_owner_cause` and 3 more.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `0a968e67`. Correct or squash the originating commit before retaining this point in history.
