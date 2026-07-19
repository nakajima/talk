# Commit 079: `a936bb64` - Land mut parameters through dynamic dispatch

| Field | Value |
|---|---|
| Commit | `a936bb6483aab11d8140eeb3bb731f43f3955199` |
| Parent reviewed | `c76f843154c85e6be1aaa43b6f299ffbd49b90cf` |
| Author date | 2026-07-16T17:36:21-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +93 / -52 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

The consolidated writeback machinery now serves the last holdout:
mut (exclusive-borrow) parameters on dynamically dispatched
requirements. The rigid-dictionary path previously rejected them; the
existential path silently lost the mutation (verified by probe —
a.add_into(mut sum) left sum at 0). Both sites now use
compile_call_args + writeback_targets + apply_writebacks, so receiver
and parameter slots land in callee order — pinned by a test observing
(result, final self, final mut values…) across two calls — and owned
arguments transfer to dynamic callees the same way direct calls do.

931 workspace tests pass.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 1 files (+75/-50): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+13/-0): `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+5/-2): `docs/lean-rebuild-wave-reports.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 75 | 50 |
| `tests/talk_tests.rs` | 13 | 0 |
| `docs/lean-rebuild-wave-reports.md` | 5 | 2 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn run_dispatches_constrained_generic_effects() {`
- `fn run_executes_existential_values() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (1s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (9s).
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 931 workspace tests pass.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
