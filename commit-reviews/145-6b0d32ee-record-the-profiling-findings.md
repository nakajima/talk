# Commit 145: `6b0d32ee` - Record the profiling findings

| Field | Value |
|---|---|
| Commit | `6b0d32ee9b30a208e1a17dd6ced8032418f946c7` |
| Parent reviewed | `7bc48b90e50f53c881461328754d2a89b53062ed` |
| Author date | 2026-07-18T00:57:14-07:00 |
| Author | Pat Nakajima |
| Patch size | 1 files, +114 / -0 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Current-state numbers, per-instruction implementation costs from
delta microbenchmarks, the dispatch-floor and arith function-pointer
findings, and the ranked opportunity list.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 1.
- Documentation and plans: 1 files (+114/-0): `docs/profiling-findings.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `docs/profiling-findings.md` | 114 | 0 |

## Test and validation review

- Historical checkout compilation was not repeated because this patch changes only documentation/language fixtures/oracles and no Rust or Cargo inputs.
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (36s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
