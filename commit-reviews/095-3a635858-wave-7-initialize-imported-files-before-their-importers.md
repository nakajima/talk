# Commit 095: `3a635858` - Wave 7: initialize imported files before their importers

| Field | Value |
|---|---|
| Commit | `3a6358583d755c8c279098947f8ae1f9cd2c821f` |
| Parent reviewed | `edd2130ffcf9689f7d52a0152f0b85a374fdfdc9` |
| Author date | 2026-07-17T03:39:13-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +65 / -10 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Multi-file scripts composed files in discovery order, so a root file's
statements ran before an imported sibling's top-level bindings
initialized (the Imports arena trap: a global read of a never-stored
Boxed cell). files_in_initialization_order topo-sorts a program's
files by their local-import edges — dependency-first, discovery order
otherwise, cycle-tolerant — and both the script and named-entry paths
compose through it (LINK-02). The G5 examples burn-down list is empty:
all 16 pinned examples pass.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+63/-6): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+2/-4): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 63 | 6 |
| `tests/talk_tests.rs` | 2 | 4 |

### Representative declarations touched

- `pub(crate) struct ProgramInput<'a> {`
- `fn files_in_initialization_order`
- `impl<'a> ProgramBuilder<'a> {`
- `fn talk_test_runs_acceptance_projects() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (16s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
