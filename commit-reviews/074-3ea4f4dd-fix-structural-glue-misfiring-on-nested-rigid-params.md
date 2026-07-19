# Commit 074: `3ea4f4dd` - Fix structural glue misfiring on nested rigid params

| Field | Value |
|---|---|
| Commit | `3ea4f4dd7a49554a6c36947b0fca76c0fb100a03` |
| Parent reviewed | `8957d04de54915d10a93ac396e81ed2fa5972e8a` |
| Author date | 2026-07-16T12:34:02-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +33 / -3 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

A rigid effect-generic param nested inside an aggregate holds a raw
Copy value (the perform site rejects owned shapes under nested generic
positions) — only a value typed directly as the param is a perform-site
package. The tuple recursion in needs_drop/drop_value/retain_value
treated nested params as packages and called existential glue on raw
values, trapping at runtime on e.g. a `(Int, T)` payload; it now skips
them, with both sides pinned by tests.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+17/-3): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+16/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 17 | 3 |
| `tests/talk_tests.rs` | 16 | 0 |

### Representative declarations touched

- `fn needs_drop_inner(builder: &ProgramBuilder<'_>, ty: &Ty, borrowed: bool) -> bo`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn run_passes_owned_payloads_through_generic_effects() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (9s).
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
