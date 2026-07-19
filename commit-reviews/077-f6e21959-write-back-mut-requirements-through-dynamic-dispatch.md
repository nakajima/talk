# Commit 077: `f6e21959` - Write back mut requirements through dynamic dispatch

| Field | Value |
|---|---|
| Commit | `f6e219599a972d48368f41d963dbb2c10296022d` |
| Parent reviewed | `d5e822df2fe1803703bd0edec0f410014f7addbe` |
| Author date | 2026-07-16T17:05:35-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +160 / -7 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Probing "mut requirements on rigid receivers" showed the prior guard
never fired — member callee types exclude the receiver, so a mut
requirement called on a rigid value ran and silently lost its
receiver mutation (or trapped downstream on the writeback tuple). The
same defect existed for existential receivers, hidden behind a second
bug: constructions coerced into existentials resolved the coercion
target instead of the payload type and rejected.

All three now execute, pinned by tests that observe the mutation
across two calls:

- The requirement's declared scheme (exclusive-borrow receiver) marks
  `mut func` requirements, so every implementation follows the
  (result, final self) convention.
- Rigid dispatch unpacks the pair and writes the evolved receiver back
  through its place chain.
- Existential dispatch rebuilds the existential around the evolved
  payload with its own witness table and writes it back.
- Constructions under an existential coercion build the pack's payload
  type.

`mut` parameters beyond the receiver stay rejected on dynamic paths —
there is no argument-writeback convention there yet.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 1 files (+137/-5): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+14/-0): `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+9/-2): `docs/lean-rebuild-wave-reports.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 137 | 5 |
| `tests/talk_tests.rs` | 14 | 0 |
| `docs/lean-rebuild-wave-reports.md` | 9 | 2 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn requirement_is_mut`
- `fn run_dispatches_constrained_generic_effects() {`
- `fn run_executes_existential_values() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (10s).
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 931 workspace tests + 4 Swift tests pass.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
