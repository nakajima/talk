# Commit 103: `86ed9da7` - Support explicit initializers on 'heap structs; fix heap retain glue

| Field | Value |
|---|---|
| Commit | `86ed9da7d96684a706ad080a56eebdf4551f365d` |
| Parent reviewed | `6edd8e81d9d83479b742ffadcb1ecce0af4f0e89` |
| Author date | 2026-07-17T08:11:52-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +79 / -3 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

An explicit init now runs over a fresh object as self, mirroring the
value path's fresh-record call (with the Deinit finalizer installed at
creation), unblocking Dict and the http_router programs. Retaining a
'heap handle now acquires a region claim instead of recursing
structurally through fields - a recursive node type (DictNode) sent
the compiler into unbounded glue emission. The remaining dict/router
entries on the flow burn-down are region-claim accounting during
chain-moving inserts, no longer compile failures.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+79/-2): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+0/-1): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 79 | 2 |
| `tests/talk_tests.rs` | 0 | 1 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (25s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
