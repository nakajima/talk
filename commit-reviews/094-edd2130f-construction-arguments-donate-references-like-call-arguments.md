# Commit 094: `edd2130f` - Construction arguments donate references like call arguments

| Field | Value |
|---|---|
| Commit | `edd2130ffcf9689f7d52a0152f0b85a374fdfdc9` |
| Parent reviewed | `a56136fa17c249eb4132422fee4f109f3c2ca7cb` |
| Author date | 2026-07-17T03:29:48-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +57 / -4 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

compile_construction consumed operands with bare consume_operand, so a
field read passed to a construction moved the buffer out from under its
owner (the talk-syntax for_stmt double free: Block(body:
copy_block(body).body, ...)). Both construction paths now consume_into
— retaining operands the frame does not own — except for
Borrowed-classified view types (UTF8View, Substring), whose
constructions never take ownership of what they look into. Adds an
alloc-site line and TALK_TRACE_MEM_PTR site windows to the memory
trace.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+24/-4): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+33/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `tests/talk_tests.rs` | 33 | 0 |
| `src/backend/mir.rs` | 24 | 4 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn run_keeps_arm_bindings_across_inner_statements() {`
- `fn run_retains_field_reads_consumed_by_constructions`
- `struct Box2`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (12s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `run_retains_field_reads_consumed_by_constructions`.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
