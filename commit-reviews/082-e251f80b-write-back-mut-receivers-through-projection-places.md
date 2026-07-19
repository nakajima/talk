# Commit 082: `e251f80b` - Write back mut receivers through projection places

| Field | Value |
|---|---|
| Commit | `e251f80bf62c1559fbe072c56aea6fb0ea1b8ffd` |
| Parent reviewed | `2c018644b7fdc02aa2013239ade95ac2c129002c` |
| Author date | 2026-07-16T20:14:49-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +38 / -24 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

self.comments.push(comment) silently lost its receiver mutation: the
member-call path resolved receiver places for bare variables and global
loads only, so a projected receiver produced no writeback target and
apply_writebacks skipped it — the evolved array never landed, and the
enclosing frame later double-freed the stale storage the push had
already released (talk-syntax's comment capture crashed on this).
Receiver places now resolve through the same place chains mut arguments
and assignments use, covering bindings, globals, and projection spines.

Also adds a memory event trace (TALK_TRACE_MEM: allocs, frees, and
per-free chunk/pc sites) and includes the pointer in double-free traps.

932 workspace tests pass; talk-syntax's lexing suite passes through the
comment-capture tests (deeper parser suites still under investigation).

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 2 files (+31/-24): `src/backend/mir.rs`, `talk-runtime/src/interp.rs`.
- Tests and test oracles: 1 files (+7/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 7 | 21 |
| `talk-runtime/src/interp.rs` | 24 | 3 |
| `tests/talk_tests.rs` | 7 | 0 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn run_loop(module: &Module, machine: &mut Machine) -> Result<Value, String> {`
- `impl Machine<'_> {`
- `fn exec_local(`
- `fn run_dispatches_constrained_generic_effects() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (13s).
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 932 workspace tests pass; talk-syntax's lexing suite passes through the

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
