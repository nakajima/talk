# Commit 122: `bbacd632` - Linear path-sensitivity: consuming methods and abort cleanup

| Field | Value |
|---|---|
| Commit | `bbacd632ac8c56d7ad65ef902fc2da9a0a7eda5d` |
| Parent reviewed | `449d0a0d205a7432d37637790b07cb014bc07903` |
| Author date | 2026-07-17T12:32:06-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +22 / -8 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

A consuming method's drop of its own receiver IS the linear value's
consumption; abort-unwind cleanup blocks may tear linear values down
(the abort is their end of life). With the loop/branch merge machinery
already path-sensitive, all four linear rules pass: consuming-method
disposal, consumption after a loop with breaks, scope-exit drop
rejection, and one-branch-only move rejection.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 4.
- Production Rust: 1 files (+20/-2): `src/backend/mir.rs`.
- Tests and test oracles: 3 files (+2/-6): `tests/reference/flow/expected/linear_value_dropped_at_scope_exit_is_rejected.error`, `tests/reference/flow/expected/linear_value_moved_in_one_branch_only_is_rejected.error`, `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 20 | 2 |
| `tests/talk_tests.rs` | 0 | 4 |
| `tests/reference/flow/expected/linear_value_moved_in_one_branch_only_is_rejected.error` | 1 | 1 |
| `tests/reference/flow/expected/linear_value_dropped_at_scope_exit_is_rejected.error` | 1 | 1 |

### Representative declarations touched

- `impl<'a> ProgramBuilder<'a> {`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (37s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/reference/flow/expected/linear_value_dropped_at_scope_exit_is_rejected.error`, `tests/reference/flow/expected/linear_value_moved_in_one_branch_only_is_rejected.error`, `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
