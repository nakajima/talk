# Commit 106: `ccd405fc` - Merge break-path ownership states at loop exits

| Field | Value |
|---|---|
| Commit | `ccd405fcf7cd12013c3006bf79c81faf4dedea90` |
| Parent reviewed | `7f6f4d0a339c5b839ffe6970abae5dc2ab4692ef` |
| Author date | 2026-07-17T09:29:16-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +53 / -6 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

A local moved on one break path but not another dropped
unconditionally after the loop (compile-order state won). Breaks now
record their end state in the loop frame and the exit merges them
through merge_arms exactly like if-arms at a join - divergent locals
drop on the paths that still own them. The condition's normal exit
carries the conservative union of entry and back-edge states.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+53/-5): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+0/-1): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 53 | 5 |
| `tests/talk_tests.rs` | 0 | 1 |

### Representative declarations touched

- `struct LoopFrame {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (27s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
