# Commit 096: `075a5659` - Make file initialization order insertion-stable

| Field | Value |
|---|---|
| Commit | `075a5659164bc6ff08364080b7ae90023c1e1c6d` |
| Parent reviewed | `3a6358583d755c8c279098947f8ae1f9cd2c821f` |
| Author date | 2026-07-17T03:45:07-07:00 |
| Author | Pat Nakajima |
| Patch size | 1 files, +18 / -17 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

The layer-based ordering let dependency-free files jump ahead of
dependent ones, moving the test harness postlude (whose value is the
suite result) out of last place. Depth-first emission keeps every
file at its discovery position except that its imports hoist ahead
of it.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 1.
- Production Rust: 1 files (+18/-17): `src/backend/mir.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 18 | 17 |

### Representative declarations touched

- `fn files_in_initialization_order(program: &TypedProgram) -> Vec<&crate::typed_as`
- `fn visit`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (15s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- No test files or executable language test fixtures changed in this patch.
- Coverage note: production behavior changes without a directly changed test surface in this commit; confidence therefore comes from existing suites and later integration coverage.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
