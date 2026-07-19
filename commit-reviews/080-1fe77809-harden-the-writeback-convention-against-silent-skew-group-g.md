# Commit 080: `1fe77809` - Harden the writeback convention against silent skew (group G)

| Field | Value |
|---|---|
| Commit | `1fe778091780aae90bdcf24f0cff86b6d433ba33` |
| Parent reviewed | `a936bb6483aab11d8140eeb3bb731f43f3955199` |
| Author date | 2026-07-16T17:54:12-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +199 / -2 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Three writeback bugs in a row had one shape: the convention crossing a
dynamic boundary at feature intersections the per-feature tests never
crossed. This makes the intersections systematically hostile:

- Probing first found one more: mut arguments on performs were
  silently ignored. Clauses now register exclusive-borrow declared
  params as writebacks, and performs land evolved values through the
  shared machinery — effects follow the same convention as every
  other call shape.
- A table-driven writeback matrix test crosses call shapes (direct,
  method, closure, global fn value, rigid dictionary, existential,
  perform) with mutation shapes (mut receiver, one/two mut params,
  both, projected places) and owned-value transfer; each cell makes
  two calls and observes evolved state, with the runtime's allocation
  balance checking ownership per cell.
- A compile-time convention validator: instances record their
  writeback width; named call sites and requirement-closure
  selections record the width they expect; any disagreement after the
  worklist drains is a compile error, so declared-vs-implementation
  shape skew can no longer be silent.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 1 files (+89/-2): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+80/-0): `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+30/-0): `docs/lean-rebuild-wave-reports.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 89 | 2 |
| `tests/talk_tests.rs` | 80 | 0 |
| `docs/lean-rebuild-wave-reports.md` | 30 | 0 |

### Representative declarations touched

- `struct ProgramBuilder<'a> {`
- `impl<'a> ProgramBuilder<'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn run_clones_enum_values_with_payloads() {`
- `fn writeback_matrix_covers_call_shapes_and_mutation_shapes`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (13s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `writeback_matrix_covers_call_shapes_and_mutation_shapes`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 932 workspace tests + 4 Swift tests pass.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
