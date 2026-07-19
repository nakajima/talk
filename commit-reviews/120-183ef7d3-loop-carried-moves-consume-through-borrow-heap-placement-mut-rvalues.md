# Commit 120: `183ef7d3` - Loop-carried moves, consume-through-borrow, heap placement, mut rvalues

| Field | Value |
|---|---|
| Commit | `183ef7d3fec7312da590ecc594fbcda28895a68c` |
| Parent reviewed | `42128034d4dea23b5c32b588f960d19a9ca763d1` |
| Author date | 2026-07-17T12:17:57-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +96 / -14 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Eight more rules: a value moved on the looping path (through the
back-edge or any continue) that the body reads again rejects on
re-entry - only values that outlive an iteration count, body-declared
locals are fresh every pass; `consume` of a borrowed source rejects
(the for-loop's consume mode elaborates through the same binding); a
`mut` parameter requires a mutable place argument (rvalue evolution is
unobservable); `'heap` values cannot enter existentials (no region
claim in the witness table) or raw Array storage (unscanned buffers);
and use-before-initializer keeps its stricter fail-closed rejection,
repinned.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 4.
- Production Rust: 1 files (+94/-4): `src/backend/mir.rs`.
- Tests and test oracles: 3 files (+2/-10): `tests/reference/flow/expected/consume_for_source_used_after_loop_is_rejected.error`, `tests/reference/flow/expected/rejects_use_before_initializer.error`, `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 94 | 4 |
| `tests/talk_tests.rs` | 0 | 8 |
| `tests/reference/flow/expected/rejects_use_before_initializer.error` | 1 | 1 |
| `tests/reference/flow/expected/consume_for_source_used_after_loop_is_rejected.error` | 1 | 1 |

### Representative declarations touched

- `struct LoopFrame {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (37s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/reference/flow/expected/consume_for_source_used_after_loop_is_rejected.error`, `tests/reference/flow/expected/rejects_use_before_initializer.error`, `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
