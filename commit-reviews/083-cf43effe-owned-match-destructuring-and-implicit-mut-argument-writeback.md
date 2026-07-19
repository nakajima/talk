# Commit 083: `cf43effe` - Owned-match destructuring and implicit mut-argument writeback

| Field | Value |
|---|---|
| Commit | `cf43effe5aa74145b6a7f8924a9d11275eb4e0ca` |
| Parent reviewed | `e251f80bf62c1559fbe072c56aea6fb0ea1b8ffd` |
| Author date | 2026-07-16T21:14:10-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +256 / -29 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Two more ownership-semantics completions from the talk-syntax corpus:

- An owned match scrutinee is consumed by destructuring (the checker's
  clone-before-reuse model): binds become arm-owned temporaries (the
  existing merge machinery drops unconsumed ones path-sensitively) and
  each matched arm releases the payloads it leaves unbound,
  re-extracted from the intact scrutinee register. Previously a payload
  escaping an owned match (`match item { .text(piece) -> piece }`) was
  double-freed — once through the escaping bind, once through the
  scrutinee's structural drop. Borrowed scrutinees keep alias
  semantics. Or-patterns leaving owned payloads unbound on a consumed
  value reject explicitly (the arm cannot know which alternative
  matched).
- The checker passes place arguments to `mut` parameters without
  requiring the call-site marker; the backend only captured writeback
  places for marked arguments, so `push_node(work, root)` silently
  discarded the evolved array and the caller kept (and later re-freed)
  storage the callee's growth had already released. writeback_targets
  now resolves the place from the argument expression for every
  exclusive-borrow parameter; rvalue arguments still drop their
  evolution unobservably.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 4.
- Production Rust: 3 files (+241/-29): `src/backend/mir.rs`, `src/compiling/package.rs`, `talk-runtime/src/interp.rs`.
- Tests and test oracles: 1 files (+15/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 222 | 22 |
| `talk-runtime/src/interp.rs` | 15 | 3 |
| `tests/talk_tests.rs` | 15 | 0 |
| `src/compiling/package.rs` | 4 | 4 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn settle_owned_match`
- `fn pattern_leaves_owned_unbound`
- `impl PackageProject {`
- `fn run_loop(module: &Module, machine: &mut Machine) -> Result<Value, String> {`
- `fn exec_local(`
- `fn run_dispatches_constrained_generic_effects() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (13s).
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 932 workspace tests pass; talk-syntax progresses further into its

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
