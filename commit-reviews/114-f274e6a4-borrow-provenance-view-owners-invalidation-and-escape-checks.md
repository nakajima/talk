# Commit 114: `f274e6a4` - Borrow provenance: view owners, invalidation, and escape checks

| Field | Value |
|---|---|
| Commit | `f274e6a46f24f5085073295def3a834bb2eecf50` |
| Parent reviewed | `8150b4b8dd68687dc3a0b90524e1c78805c0271e` |
| Author date | 2026-07-17T10:36:42-07:00 |
| Author | Pat Nakajima |
| Patch size | 8 files, +109 / -9 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

A call returning a Borrowed-classified view records the frame local it
derives from (receiver or first argument); binds, tuples, variants,
and constructions propagate the root through wrapping. Moving or
reassigning the owner invalidates its live views - reads reject with
use-of-borrowed-value - and returning a view (or borrow-carrying
container) rooted in the frame's own value rejects as an escaping
borrow. Closes the escaping-return family (substring of local and of
owned parameter, enum/struct/tuple wrappers, array borrows) and the
owner-invalidation family (after move, after reassignment, through
containers), with zero over-rejections across all gates.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 8.
- Production Rust: 1 files (+102/-2): `src/backend/mir.rs`.
- Tests and test oracles: 7 files (+7/-7): `tests/reference/flow/expected/generic_container_containing_borrow_tracks_owner_invalidation.error`, `tests/reference/flow/expected/mutable_call_argument_invalidates_shared_borrow.error`, `tests/reference/flow/expected/mutable_method_receiver_invalidates_borrows_of_receiver.error`, `tests/reference/flow/expected/ordinary_borrowed_return_tracks_single_borrowed_argument_owner.error`, `tests/reference/flow/expected/rejects_borrow_use_after_owner_move.error`, `tests/reference/flow/expected/rejects_borrow_use_after_owner_reassignment.error`, `tests/reference/flow/expected/rejects_reassigned_borrow_use_after_owner_move.error`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 102 | 2 |
| `tests/reference/flow/expected/rejects_reassigned_borrow_use_after_owner_move.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_borrow_use_after_owner_reassignment.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_borrow_use_after_owner_move.error` | 1 | 1 |
| `tests/reference/flow/expected/ordinary_borrowed_return_tracks_single_borrowed_argument_owner.error` | 1 | 1 |
| `tests/reference/flow/expected/mutable_method_receiver_invalidates_borrows_of_receiver.error` | 1 | 1 |
| `tests/reference/flow/expected/mutable_call_argument_invalidates_shared_borrow.error` | 1 | 1 |
| `tests/reference/flow/expected/generic_container_containing_borrow_tracks_owner_invalidation.error` | 1 | 1 |

### Representative declarations touched

- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn borrow_root`
- `fn record_view`
- `fn propagate_view`
- `fn invalidate_views_of`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (32s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/reference/flow/expected/generic_container_containing_borrow_tracks_owner_invalidation.error`, `tests/reference/flow/expected/mutable_call_argument_invalidates_shared_borrow.error`, `tests/reference/flow/expected/mutable_method_receiver_invalidates_borrows_of_receiver.error`, `tests/reference/flow/expected/ordinary_borrowed_return_tracks_single_borrowed_argument_owner.error`, `tests/reference/flow/expected/rejects_borrow_use_after_owner_move.error`, `tests/reference/flow/expected/rejects_borrow_use_after_owner_reassignment.error`, `tests/reference/flow/expected/rejects_reassigned_borrow_use_after_owner_move.error`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
