# Commit 107: `1775a442` - Deconstruction transfers ownership to the extracted elements

| Field | Value |
|---|---|
| Commit | `1775a4423a3ca4919b3466026828e1d3866effa0` |
| Parent reviewed | `ccd405fcf7cd12013c3006bf79c81faf4dedea90` |
| Author date | 2026-07-17T09:33:15-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +17 / -4 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Destructuring an owned tuple or record consumed the source without a
drop while the element binds also donated references - each object
handle gained a claim nobody released. When the source is owned, the
extracted elements now inherit its ownership (binds consume them
outright, wildcards drop them); a borrowed source keeps ownership and
binds donate as before.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+17/-2): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+0/-2): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 17 | 2 |
| `tests/talk_tests.rs` | 0 | 2 |

### Representative declarations touched

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
