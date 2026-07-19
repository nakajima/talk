# Commit 111: `2476d132` - Track global moves; honor the explicit copy marker

| Field | Value |
|---|---|
| Commit | `2476d132ea031d46702156b22ce8930607252c33` |
| Parent reviewed | `ea797eada08916d7008b72914a72fc009826ba15` |
| Author date | 2026-07-17T09:58:26-07:00 |
| Author | Pat Nakajima |
| Patch size | 11 files, +56 / -26 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Consuming a global's value now marks the global moved - later reads
reject with use-of-moved-value and reassignment restores it, closing
the entire by-value move-discipline family (thirteen rejects: call,
method, constructor, literal, and repeated-operand positions, plus the
branch-join variant), while donation keeps the runtime balanced. The
explicit `copy` marker now clones at the argument site (fresh local,
structural retain), so the callee consumes the copy and the source
stays live - the reference's copy_marker_clones_and_balances_frees.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 11.
- Production Rust: 1 files (+47/-4): `src/backend/mir.rs`.
- Tests and test oracles: 10 files (+9/-22): `tests/reference/flow/expected/consume_marker_forces_a_generic_move.error`, `tests/reference/flow/expected/match_arm_move_then_use_is_rejected.error`, `tests/reference/flow/expected/move_on_conditional_continue_path_is_use_after_move_on_reentry.error`, `tests/reference/flow/expected/rejects_use_after_generic_struct_instantiated_with_owned_field_move.error`, `tests/reference/flow/expected/rejects_use_after_simple_owned_move.error`, `tests/reference/flow/expected/rejects_use_after_struct_with_owned_field_move.error`, `tests/reference/flow/expected/rejects_use_before_initializer.error`, `tests/reference/flow/expected/rejects_whole_struct_use_after_owned_field_move.error`, and 2 more.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 47 | 4 |
| `tests/talk_tests.rs` | 0 | 13 |
| `tests/reference/flow/expected/unique_parameter_value_moves_like_owned.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_whole_struct_use_after_owned_field_move.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_use_before_initializer.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_use_after_struct_with_owned_field_move.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_use_after_simple_owned_move.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_use_after_generic_struct_instantiated_with_owned_field_move.error` | 1 | 1 |
| `tests/reference/flow/expected/move_on_conditional_continue_path_is_use_after_move_on_reentry.error` | 1 | 1 |
| `tests/reference/flow/expected/match_arm_move_then_use_is_rejected.error` | 1 | 1 |
| `tests/reference/flow/expected/consume_marker_forces_a_generic_move.error` | 1 | 1 |

### Representative declarations touched

- `struct ArmEnd {`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (31s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/reference/flow/expected/consume_marker_forces_a_generic_move.error`, `tests/reference/flow/expected/match_arm_move_then_use_is_rejected.error`, `tests/reference/flow/expected/move_on_conditional_continue_path_is_use_after_move_on_reentry.error`, `tests/reference/flow/expected/rejects_use_after_generic_struct_instantiated_with_owned_field_move.error`, `tests/reference/flow/expected/rejects_use_after_simple_owned_move.error`, `tests/reference/flow/expected/rejects_use_after_struct_with_owned_field_move.error`, `tests/reference/flow/expected/rejects_use_before_initializer.error`, `tests/reference/flow/expected/rejects_whole_struct_use_after_owned_field_move.error`, `tests/reference/flow/expected/unique_parameter_value_moves_like_owned.error`, `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
