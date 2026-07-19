# Commit 102: `6edd8e81` - Run Deinit hooks: scope-exit drops and 'heap region finalizers

| Field | Value |
|---|---|
| Commit | `6edd8e81d9d83479b742ffadcb1ecce0af4f0e89` |
| Parent reviewed | `4ca1927141da16ef3b6aead6b85f15fd5a9e6e25` |
| Author date | 2026-07-17T04:27:23-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +37 / -4 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Deinit-conforming types never got their drops scheduled unless a field
owned a buffer (needs_drop ignored the conformance), and 'heap objects
never installed finalizers at all. needs_drop now schedules any
Deinit-conforming nominal, and heap construction emits the new backend
SetFinalizer over the deinit witness (the runtime's finalizer pump and
insn already existed, unused). All four reference deinit pins leave the
flow burn-down: scope exit, existential payloads, region teardown, and
deinits that allocate during teardown.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 2 files (+37/-0): `src/backend/lower.rs`, `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+0/-4): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 32 | 0 |
| `src/backend/lower.rs` | 5 | 0 |
| `tests/talk_tests.rs` | 0 | 4 |

### Representative declarations touched

- `impl Lowering<'_> {`
- `pub(crate) enum Inst {`
- `fn needs_drop_inner(builder: &ProgramBuilder<'_>, ty: &Ty, borrowed: bool) -> bo`
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
