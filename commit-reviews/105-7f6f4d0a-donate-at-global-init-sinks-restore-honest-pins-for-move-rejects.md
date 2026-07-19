# Commit 105: `7f6f4d0a` - Donate at global-init sinks; restore honest pins for move rejects

| Field | Value |
|---|---|
| Commit | `7f6f4d0a339c5b839ffe6970abae5dc2ab4692ef` |
| Parent reviewed | `34fe510548a7d99adbe2d57fde6dc4a23f03cecb` |
| Author date | 2026-07-17T09:25:14-07:00 |
| Author | Pat Nakajima |
| Patch size | 10 files, +20 / -9 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Script-level `let t = s` consumed with bare consume_operand, aliasing
two global slots over one reference count - the replacement-drop and
teardown then double-freed (the reassignment/field-restore trio now
prints its reference values). The wording repin pass had captured
eight runtime crashes as "diagnostics"; those pins are restored to the
reference needles and the entries moved onto the burn-down where they
belong - they are the by-value move-discipline family this backend
does not yet enforce (donation makes the programs run; the reference
rejects them).

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 10.
- Production Rust: 1 files (+4/-1): `src/backend/mir.rs`.
- Tests and test oracles: 9 files (+16/-8): `tests/reference/flow/expected/move_on_conditional_continue_path_is_use_after_move_on_reentry.error`, `tests/reference/flow/expected/rejects_function_assigning_a_globally_borrowed_global.error`, `tests/reference/flow/expected/rejects_raw_pointer_usage_in_safe_source.error`, `tests/reference/flow/expected/rejects_use_after_generic_struct_instantiated_with_owned_field_move.error`, `tests/reference/flow/expected/rejects_use_after_simple_owned_move.error`, `tests/reference/flow/expected/rejects_use_after_struct_with_owned_field_move.error`, `tests/reference/flow/expected/rejects_use_before_initializer.error`, `tests/reference/flow/expected/rejects_whole_struct_use_after_owned_field_move.error`, and 1 more.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `tests/talk_tests.rs` | 8 | 0 |
| `src/backend/mir.rs` | 4 | 1 |
| `tests/reference/flow/expected/rejects_whole_struct_use_after_owned_field_move.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_use_before_initializer.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_use_after_struct_with_owned_field_move.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_use_after_simple_owned_move.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_use_after_generic_struct_instantiated_with_owned_field_move.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_raw_pointer_usage_in_safe_source.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_function_assigning_a_globally_borrowed_global.error` | 1 | 1 |
| `tests/reference/flow/expected/move_on_conditional_continue_path_is_use_after_move_on_reentry.error` | 1 | 1 |

### Representative declarations touched

- `impl<'a> ProgramBuilder<'a> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (24s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/reference/flow/expected/move_on_conditional_continue_path_is_use_after_move_on_reentry.error`, `tests/reference/flow/expected/rejects_function_assigning_a_globally_borrowed_global.error`, `tests/reference/flow/expected/rejects_raw_pointer_usage_in_safe_source.error`, `tests/reference/flow/expected/rejects_use_after_generic_struct_instantiated_with_owned_field_move.error`, `tests/reference/flow/expected/rejects_use_after_simple_owned_move.error`, `tests/reference/flow/expected/rejects_use_after_struct_with_owned_field_move.error`, `tests/reference/flow/expected/rejects_use_before_initializer.error`, `tests/reference/flow/expected/rejects_whole_struct_use_after_owned_field_move.error`, `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
