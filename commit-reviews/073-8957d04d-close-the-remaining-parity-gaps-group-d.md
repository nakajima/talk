# Commit 073: `8957d04d` - Close the remaining parity gaps (group D)

| Field | Value |
|---|---|
| Commit | `8957d04de54915d10a93ac396e81ed2fa5972e8a` |
| Parent reviewed | `95d1f6cf052acbbf7c95ee09d1796df0b5edc31d` |
| Author date | 2026-07-16T10:33:20-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +288 / -101 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Re-audited every remaining rejection against the ledger's Required
rows; the two genuine gaps now execute:

- EFF-03: owned payloads through directly-generic effect positions.
  The perform site wraps the payload in an existential-shaped
  [drop, retain] package (the DYN-01 convention without protocol
  requirements), so one clause body serves every instantiation:
  unconsumed payloads release through the drop slot at clause exit,
  `continue payload` hands the package back for the perform site to
  unwrap, and discontinue cleanup drops it like any owned local.
  Clause binders take ownership types from the effect's declared
  signature, closing a leak for unannotated owned binders.
- CLO-02: `mut` parameters on function values. Indirect calls compile
  through one shared path and derive the writeback convention from the
  function type alone, matching direct calls.

Linear globals get a precise, principled rejection (exactly-once
consumption cannot be proven across every reader plus teardown) in
place of a teardown-artifact diagnostic. CHG-06 owned captures and
ambient-effect user handlers stay rejected because the ledger requires
rejection there.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 4.
- Production Rust: 1 files (+204/-82): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+35/-15): `tests/talk_tests.rs`.
- Documentation and plans: 2 files (+49/-4): `docs/backend-parity-ledger.md`, `docs/lean-rebuild-wave-reports.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 204 | 82 |
| `tests/talk_tests.rs` | 35 | 15 |
| `docs/lean-rebuild-wave-reports.md` | 36 | 0 |
| `docs/backend-parity-ledger.md` | 13 | 4 |

### Representative declarations touched

- `fn needs_drop_inner(builder: &ProgramBuilder<'_>, ty: &Ty, borrowed: bool) -> bo`
- `impl<'a> ProgramBuilder<'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn compile_indirect_call`
- `fn pack_effect_payload`
- `fn run_executes_mut_arguments() {`
- `fn run_tears_down_globals_after_a_top_level_discontinue() {`
- `fn run_passes_owned_payloads_through_generic_effects`
- `fn run_rejects_unsupported_source_forms_explicitly() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (10s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `run_passes_owned_payloads_through_generic_effects`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 925 workspace tests + 4 Swift tests pass; total <=11,834 of the

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
