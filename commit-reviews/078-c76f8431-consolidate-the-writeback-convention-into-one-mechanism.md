# Commit 078: `c76f8431` - Consolidate the writeback convention into one mechanism

| Field | Value |
|---|---|
| Commit | `c76f843154c85e6be1aaa43b6f299ffbd49b90cf` |
| Parent reviewed | `f6e219599a972d48368f41d963dbb2c10296022d` |
| Author date | 2026-07-16T17:31:48-07:00 |
| Author | Pat Nakajima |
| Patch size | 1 files, +188 / -189 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

The (result, final mut values…) convention was hand-rolled at four
call sites (named calls, indirect calls, rigid-dictionary dispatch,
existential dispatch) plus two identical mut-argument capture loops.
One mechanism now owns it:

- WritebackTarget: where an evolved value lands — straight into its
  place, or rebuilt as an existential around the evolved payload
  first.
- compile_call_args: argument compilation with mut-place capture.
- writeback_targets: the caller half — one target per
  exclusive-borrow parameter, receiver slot first, mirroring the
  callee's writeback_params order.
- apply_writebacks: the landing half — unpack the pair and store each
  evolved value through write_place.

All four call sites are now thin users of the same helpers; the
callee half (writeback_params + emit_return) was already single-site.
Net diff -1 line with the duplication gone. 931 workspace tests pass.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 1.
- Production Rust: 1 files (+188/-189): `src/backend/mir.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 188 | 189 |

### Representative declarations touched

- `struct PlaceChain {`
- `enum WritebackTarget`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn compile_call_args`
- `fn writeback_targets`
- `fn apply_writebacks`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (11s).
- `git diff --check` passed for this commit against its first parent.
- No test files or executable language test fixtures changed in this patch.
- Author-reported validation (not independently treated as proof for the exact commit):
  - Net diff -1 line with the duplication gone. 931 workspace tests pass.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
