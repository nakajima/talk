# Commit 081: `2c018644` - Fix cross-program symbol stamping and five backend gaps from talk-syntax

| Field | Value |
|---|---|
| Commit | `2c018644b7fdc02aa2013239ade95ac2c129002c` |
| Parent reviewed | `1fe778091780aae90bdcf24f0cff86b6d433ba33` |
| Author date | 2026-07-16T20:00:52-07:00 |
| Author | Pat Nakajima |
| Patch size | 6 files, +817 / -72 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Running a real package (talk-syntax) surfaced a fundamental soundness
hole plus a cluster of gaps the corpus never reached:

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 6.
- Production Rust: 6 files (+817/-72): `src/backend/mir.rs`, `src/compiling/driver.rs`, `src/compiling/module.rs`, `src/compiling/package.rs`, `src/testing.rs`, `talk-runtime/src/interp.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 771 | 58 |
| `src/compiling/package.rs` | 14 | 12 |
| `src/compiling/driver.rs` | 11 | 1 |
| `talk-runtime/src/interp.rs` | 9 | 1 |
| `src/testing.rs` | 7 | 0 |
| `src/compiling/module.rs` | 5 | 0 |

### Representative declarations touched

- `struct ProgramBuilder<'a> {`
- `impl<'a> ProgramBuilder<'a> {`
- `fn effect_sig`
- `fn display_name`
- `fn protocol_named`
- `fn variant_names`
- `fn field_names`
- `fn derived_show`
- `fn derived_equality`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn emit_string_lit`
- `fn emit_string_concat`
- `fn emit_sub_show`
- `fn emit_show`
- `fn emit_equality`
- `fn emit_field_equality`
- `fn emit_enum_equality`
- `impl Driver<Typed> {`
- ...and 4 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (3s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (15s).
- `git diff --check` passed for this commit against its first parent.
- No test files or executable language test fixtures changed in this patch.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 932 workspace tests pass. talk-syntax progresses from failing to

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
