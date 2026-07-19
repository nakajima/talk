# Commit 100: `6ab0c3ec` - Wave 3: port the reference flow-rule corpus as a measured gate

| Field | Value |
|---|---|
| Commit | `6ab0c3eccb155780c228f28b0da772ef688a2d44` |
| Parent reviewed | `bdc7190ed5c37dd6f63eade241a66ba2830c6175` |
| Author date | 2026-07-17T04:21:43-07:00 |
| Author | Pat Nakajima |
| Patch size | 367 files, +1942 / -0 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

183 of the reference's 219 flow/ownership tests land as
tests/reference/flow (110 accepts with stdout pins, 73 rejects with
diagnostic-fragment pins; 37 were capture tests already ported,
compiler-internal fixtures, or unpinnable). The gate enforces 101
today; the 82-name burn-down list may only shrink. Reject pins carry
this compiler's own diagnostic fragments where the rule already fires
under different wording; declaration-only accepts count as
compile-checked (demand-driven compilation checks what runs - an
argued divergence from the reference's whole-program pass).

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 366, M: 1.
- Tests and test oracles: 367 files (+1942/-0): `tests/reference/flow/allows_borrowed_field_in_struct_type.tlk`, `tests/reference/flow/allows_borrowed_payload_in_enum_type.tlk`, `tests/reference/flow/allows_character_literal_global.tlk`, `tests/reference/flow/allows_copy_field_read_from_shared_borrow.tlk`, `tests/reference/flow/allows_copy_value_reuse_after_assignment.tlk`, `tests/reference/flow/allows_function_typed_field_with_borrow_params.tlk`, `tests/reference/flow/allows_global_iterator_over_global_array.tlk`, `tests/reference/flow/allows_mut_receiver_call_through_owned_field_in_mut_func.tlk`, and 359 more.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `tests/talk_tests.rs` | 161 | 0 |
| `tests/reference/flow/for_loop_block_arg_matched_in_body_is_accepted.tlk` | 43 | 0 |
| `tests/reference/flow/heap_deinit_creating_objects_nests_teardown.tlk` | 26 | 0 |
| `tests/reference/flow/existential_payload_deinit_runs.tlk` | 21 | 0 |
| `tests/reference/flow/for_over_enum_array_with_match_runs.tlk` | 20 | 0 |
| `tests/reference/flow/generic_heap_extraction_retains_cheap_clone_enum_payloads.tlk` | 18 | 0 |
| `tests/reference/flow/dict_inserts_and_looks_up.tlk` | 18 | 0 |
| `tests/reference/flow/tuple_match_on_borrowed_enums_preserves_payload_owners.tlk` | 17 | 0 |
| `tests/reference/flow/per_iteration_mutable_borrow_can_end_before_mutation.tlk` | 17 | 0 |
| `tests/reference/flow/move_on_conditional_continue_path_is_use_after_move_on_reentry.tlk` | 17 | 0 |
| `tests/reference/flow/match_on_borrowed_enum_neither_leaks_nor_double_frees.tlk` | 17 | 0 |
| `tests/reference/flow/loop_carried_mutable_borrow_lives_until_storage_dead.tlk` | 17 | 0 |
| `tests/reference/flow/linear_consumed_after_a_loop_with_break_is_accepted.tlk` | 17 | 0 |
| `tests/reference/flow/heap_deinit_runs_at_region_teardown.tlk` | 17 | 0 |
| `tests/reference/flow/generic_heap_extraction_clones_per_instantiation.tlk` | 17 | 0 |

### Representative declarations touched

- `struct View`
- `enum View`
- `struct Person`
- `struct Mapper`
- `struct Inner`
- `struct Outer`
- `struct Wrapper`
- `struct Point`
- `struct Box`
- `enum Box2`
- `struct Item`
- `struct Ref`
- `struct Sink`
- `struct Socket`
- `struct Holder`
- `struct Guard`
- `struct Node`
- `enum E`
- ...and 16 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (1s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (23s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `assert_flow_corpus`, `reference_flow_corpus_holds`.
- Added Talk/expected-output fixtures: `tests/reference/flow/allows_borrowed_field_in_struct_type.tlk`, `tests/reference/flow/allows_borrowed_payload_in_enum_type.tlk`, `tests/reference/flow/allows_character_literal_global.tlk`, `tests/reference/flow/allows_copy_field_read_from_shared_borrow.tlk`, `tests/reference/flow/allows_copy_value_reuse_after_assignment.tlk`, `tests/reference/flow/allows_function_typed_field_with_borrow_params.tlk`, `tests/reference/flow/allows_global_iterator_over_global_array.tlk`, `tests/reference/flow/allows_mut_receiver_call_through_owned_field_in_mut_func.tlk`, `tests/reference/flow/allows_owner_move_after_borrow_last_use.tlk`, `tests/reference/flow/allows_raw_pointer_usage_in_unsafe_source.tlk`, `tests/reference/flow/allows_reassignment_after_owned_move.tlk`, `tests/reference/flow/allows_returning_struct_wrapping_substring_of_borrowed_parameter.tlk`, `tests/reference/flow/allows_returning_substring_of_borrowed_parameter.tlk`, `tests/reference/flow/allows_reuse_after_copy_struct_assignment.tlk`, `tests/reference/flow/allows_reuse_after_generic_struct_instantiated_with_copy_field_assignment.tlk`, `tests/reference/flow/allows_sibling_field_after_owned_field_move.tlk` and 350 more.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
