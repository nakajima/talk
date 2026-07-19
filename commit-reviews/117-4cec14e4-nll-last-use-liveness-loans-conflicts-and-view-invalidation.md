# Commit 117: `4cec14e4` - NLL last-use liveness: loans, conflicts, and view invalidation

| Field | Value |
|---|---|
| Commit | `4cec14e47ba14e204236143a4deacf60866d54c0` |
| Parent reviewed | `85750ccd8d162b7849f5eddef93792d53a7c8f25` |
| Author date | 2026-07-17T11:08:41-07:00 |
| Author | Pat Nakajima |
| Patch size | 9 files, +200 / -31 |
| Review result | **Standalone defect, repaired later** |

## Intent and sequence context

The frame scan now counts source-order variable uses; each compiled
read spends one, so a loan is live exactly until its view's last use
(RFC 2094's model, source-order approximation). Live-loan conflicts:
reading a mut-borrowed owner, mutating a shared-borrowed one, and
moving any borrowed owner all reject with the loan named. Mut
arguments and receivers (marked or not - taken from the writeback
targets) kill views of the mutated place; field reads propagate
provenance so views derived through fields track the whole value; and
invalidation strikes only genuinely view-typed locals, so owned
donations survive their source's move (the guard that keeps
talk-syntax and the corpus accept-side green). Closes the eight-rule
borrow-conflict family.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 9.
- Production Rust: 1 files (+193/-16): `src/backend/mir.rs`.
- Tests and test oracles: 8 files (+7/-15): `tests/reference/flow/expected/live_shared_borrow_blocks_later_mutation.error`, `tests/reference/flow/expected/move_while_mutably_borrowed_does_not_report_spurious_shared_borrow.error`, `tests/reference/flow/expected/ordinary_borrowed_return_tracks_single_borrowed_argument_owner.error`, `tests/reference/flow/expected/rejects_borrow_use_after_owner_reassignment.error`, `tests/reference/flow/expected/rejects_match_scrutinee_move_while_borrowed.error`, `tests/reference/flow/expected/rejects_owner_move_while_borrow_has_later_use.error`, `tests/reference/flow/expected/rejects_read_while_mutable_borrow_is_live.error`, `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 193 | 16 |
| `tests/talk_tests.rs` | 0 | 8 |
| `tests/reference/flow/expected/rejects_read_while_mutable_borrow_is_live.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_owner_move_while_borrow_has_later_use.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_match_scrutinee_move_while_borrowed.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_borrow_use_after_owner_reassignment.error` | 1 | 1 |
| `tests/reference/flow/expected/ordinary_borrowed_return_tracks_single_borrowed_argument_owner.error` | 1 | 1 |
| `tests/reference/flow/expected/move_while_mutably_borrowed_does_not_report_spurious_shared_borrow.error` | 1 | 1 |
| `tests/reference/flow/expected/live_shared_borrow_blocks_later_mutation.error` | 1 | 1 |

### Representative declarations touched

- `fn needs_drop_inner(builder: &ProgramBuilder<'_>, ty: &Ty, borrowed: bool) -> bo`
- `fn contains_borrow_classified`
- `fn free_locals(nodes: &[&Node], enclosing: &FxHashMap<Symbol, LocalId>) -> Vec<S`
- `fn cell_scan`
- `fn cell_scan(nodes: &[&Node]) -> (rustc_hash::FxHashSet<Symbol>, rustc_hash::FxH`
- `impl<'a> ProgramBuilder<'a> {`
- `struct Loan`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn live_loan_of`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (17s): `reference_flow_corpus_holds`, `run_enforces_capture_list_modes`.
- The persistent `run_enforces_capture_list_modes` failure is inherited from `cabfc772`. Any additional failure attributable to this patch is assessed in Findings below.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/reference/flow/expected/live_shared_borrow_blocks_later_mutation.error`, `tests/reference/flow/expected/move_while_mutably_borrowed_does_not_report_spurious_shared_borrow.error`, `tests/reference/flow/expected/ordinary_borrowed_return_tracks_single_borrowed_argument_owner.error`, `tests/reference/flow/expected/rejects_borrow_use_after_owner_reassignment.error`, `tests/reference/flow/expected/rejects_match_scrutinee_move_while_borrowed.error`, `tests/reference/flow/expected/rejects_owner_move_while_borrow_has_later_use.error`, `tests/reference/flow/expected/rejects_read_while_mutable_borrow_is_live.error`, `tests/talk_tests.rs`.

## Findings

### 1. [P1] Update diagnostic oracles with the new borrow-conflict wording

- Location: `tests/reference/flow/expected/rejects_reassigned_borrow_use_after_owner_move.error` and the related owner-move oracle
- Status: **Fixed by the next commit, `aa3e820f`**
- Impact: The new NLL conflict check intentionally emits `cannot move a value while it is borrowed as ...`, but the checked-in rejection oracle still requires `use of borrowed value`. Consequently the reference flow gate is red even though the new diagnostic is the desired behavior. `aa3e820f` updates both affected expected-error files and one wording detail in the backend.
- Evidence: The isolated `reference_flow_corpus_holds` test failed twice at this commit; the exact full suite has this failure plus the inherited capture-list failure.
- Recommended correction: Commit behavior and exact error-oracle changes together so the diagnostic migration is atomic.

## Disposition

Do not use this as an independently mergeable/bisectable commit. The cited later commit repairs the defect, but the history should ideally be squashed or reordered so every retained commit is green.
