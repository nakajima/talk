# Commit 075: `6dfabcc2` - Compile generic effect payloads via witness passing (group E)

| Field | Value |
|---|---|
| Commit | `6dfabcc21200c32fab7cc19f405debc5f49519ef` |
| Parent reviewed | `3ea4f4dd7a49554a6c36947b0fca76c0fb100a03` |
| Author date | 2026-07-16T14:29:14-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +424 / -152 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Nested generic payload positions ((Int, T), Array<T>, enum payloads)
now execute. Group D's per-value packaging is replaced by
value-witness-table passing — the design Swift's unspecialized-generics
ABI and Go's generics dictionaries (Griesemer et al., OOPSLA 2022)
converged on, dictionary passing in the type-class sense (Wadler &
Blott, POPL 1989):

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 4.
- Production Rust: 1 files (+326/-132): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+37/-8): `tests/talk_tests.rs`.
- Documentation and plans: 2 files (+61/-12): `docs/backend-parity-ledger.md`, `docs/lean-rebuild-wave-reports.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 326 | 132 |
| `tests/talk_tests.rs` | 37 | 8 |
| `docs/lean-rebuild-wave-reports.md` | 44 | 0 |
| `docs/backend-parity-ledger.md` | 17 | 12 |

### Representative declarations touched

- `fn contains_buffer_guarded(`
- `fn needs_drop_inner(builder: &ProgramBuilder<'_>, ty: &Ty, borrowed: bool) -> bo`
- `fn ty_has_projection(ty: &Ty) -> bool {`
- `fn witness_params`
- `fn walk`
- `fn solve_param`
- `struct ProgramBuilder<'a> {`
- `impl<'a> ProgramBuilder<'a> {`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn consume_binding`
- `fn append_witness_args`
- `fn run_passes_owned_payloads_through_generic_effects() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (12s).
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 925 workspace tests + 4 Swift tests pass; total <=12,007 of the

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
