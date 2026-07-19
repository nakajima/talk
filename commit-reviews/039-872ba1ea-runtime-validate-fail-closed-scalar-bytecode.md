# Commit 039: `872ba1ea` - runtime: validate fail-closed scalar bytecode

| Field | Value |
|---|---|
| Commit | `872ba1eac04ee837e9ed283c4b614a3bfddfa26e` |
| Parent reviewed | `9ba7c06abcfcfc594630536b42e9af2319b12ba1` |
| Author date | 2026-07-15T01:04:18-07:00 |
| Author | Pat Nakajima |
| Patch size | 9 files, +934 / -32 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 1, M: 8.
- Production Rust: 2 files (+839/-0): `talk-runtime/src/lib.rs`, `talk-runtime/src/scalar.rs`.
- Documentation and plans: 7 files (+95/-32): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/e1-talk-runtime-reuse-audit.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `talk-runtime/src/scalar.rs` | 838 | 0 |
| `docs/backend-status.md` | 33 | 4 |
| `docs/e1-talk-runtime-reuse-audit.md` | 12 | 21 |
| `docs/stage-0-contract-types.md` | 30 | 0 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 12 | 0 |
| `docs/backend-parity-ledger.md` | 3 | 3 |
| `docs/e1-scalar-execution-plan.md` | 3 | 2 |
| `docs/backend-parity-plan.md` | 2 | 2 |
| `talk-runtime/src/lib.rs` | 1 | 0 |

### Representative declarations touched

- `struct ValidatedBytecodeModule`
- `fn new`
- `fn render`
- `fn run`
- `fn run_counted`
- `fn module`
- `enum ScalarBytecodeError`
- `fn fmt`
- `fn validate_module`
- `fn validate_chunk`
- `fn validate_instruction`
- `fn validate_target`
- `fn checked_pool_range`
- `fn claim_range`
- `fn ensure_fully_claimed`
- `fn validate_reachable_control`
- `fn validates_and_runs_scalar_profile_with_zero_resources`
- `fn validates_scalar_cfg_calls_switches_and_conversions`
- ...and 5 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (13s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `validates_and_runs_scalar_profile_with_zero_resources`, `validates_scalar_cfg_calls_switches_and_conversions`, `rejects_every_quarantined_family`, `rejects_unsupported_constants_statics_and_unwind_data`, `rejects_malformed_control_and_pool_shapes`, `rejects_call_arity_and_invalid_registers`, `malformed_scalar_kinds_return_runtime_errors`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
