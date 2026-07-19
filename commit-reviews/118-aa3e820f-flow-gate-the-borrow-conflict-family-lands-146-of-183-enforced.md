# Commit 118: `aa3e820f` - Flow gate: the borrow-conflict family lands; 146 of 183 enforced

| Field | Value |
|---|---|
| Commit | `aa3e820f8fe415051a8a59cb8f78902a63acdd0d` |
| Parent reviewed | `4cec14e47ba14e204236143a4deacf60866d54c0` |
| Author date | 2026-07-17T11:12:34-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +3 / -3 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 1 files (+1/-1): `src/backend/mir.rs`.
- Tests and test oracles: 2 files (+2/-2): `tests/reference/flow/expected/rejects_borrow_use_after_owner_move.error`, `tests/reference/flow/expected/rejects_reassigned_borrow_use_after_owner_move.error`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `tests/reference/flow/expected/rejects_reassigned_borrow_use_after_owner_move.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_borrow_use_after_owner_move.error` | 1 | 1 |
| `src/backend/mir.rs` | 1 | 1 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (33s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/reference/flow/expected/rejects_borrow_use_after_owner_move.error`, `tests/reference/flow/expected/rejects_reassigned_borrow_use_after_owner_move.error`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
