# Commit 104: `34fe5105` - Balance region claims and heap teardown; donate on returns

| Field | Value |
|---|---|
| Commit | `34fe510548a7d99adbe2d57fde6dc4a23f03cecb` |
| Parent reviewed | `86ed9da7d96684a706ad080a56eebdf4551f365d` |
| Author date | 2026-07-17T09:20:41-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +106 / -43 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Three fixes that close nine flow burn-down entries (Dict, CoW,
cheap-clone extraction, heap string fields, the router): donation is
now solely retain_value's job - consume_into's separate RegionAcquire
double-counted claims whenever a value carried both buffers and
handles, so chained inserts kept regions alive forever; retain glue
and enum-retain guards widened from contains_buffer to buffers-or-
objects so handle-carrying interiors acquire their claims exactly
once; and 'heap finalizers are now a synthesized heap_teardown chunk
(Deinit hook, then buffer-field frees) instead of the bare deinit
witness, so object-held strings free at region death. Returning a
place read the frame does not own now donates a reference like any
owned sink - which unmasked that rule's absence once teardown stopped
compensating; core sources stay exempt (their _load/_alloc buffer
code manages references manually, like bare RawPtr).

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+106/-34): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+0/-9): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 106 | 34 |
| `tests/talk_tests.rs` | 0 | 9 |

### Representative declarations touched

- `fn head_args(ty: &Ty) -> &[Ty] {`
- `fn donates`
- `enum Glue {`
- `impl<'a> ProgramBuilder<'a> {`
- `fn heap_teardown`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (29s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
