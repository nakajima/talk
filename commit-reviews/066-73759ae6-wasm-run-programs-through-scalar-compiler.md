# Commit 066: `73759ae6` - wasm: run programs through scalar compiler

| Field | Value |
|---|---|
| Commit | `73759ae6ef9401bd56b5dd78a7e903ed521e2fc5` |
| Parent reviewed | `889992f6cb7a536b62e792f50c934a4343c81ed3` |
| Author date | 2026-07-15T21:22:00-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +172 / -12 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 3.
- Production Rust: 1 files (+170/-12): `wasm/src/lib.rs`.
- Build, packaging, and CI: 2 files (+2/-0): `Cargo.lock`, `wasm/Cargo.toml`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `wasm/src/lib.rs` | 170 | 12 |
| `wasm/Cargo.toml` | 1 | 0 |
| `Cargo.lock` | 1 | 0 |

### Representative declarations touched

- `pub fn format(source: &str) -> String {`
- `struct ProgramExecution`
- `struct ProgramRunError`
- `fn new`
- `fn runtime`
- `fn fmt`
- `fn from`
- `fn run_program_source`
- `pub fn run_program(source: &str) -> Result<Object, JsValue> {`
- `fn set_bool(obj: &Object, key: &str, value: bool) -> Result<(), JsValue> {`
- `fn rust_runner_executes_core_scalar_operators`
- `fn rust_runner_suppresses_unit_results`
- `fn rust_runner_reports_frontend_and_runtime_phases`
- `fn compiler_phase_errors_have_stable_javascript_messages`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (14s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `rust_runner_executes_core_scalar_operators`, `rust_runner_suppresses_unit_results`, `rust_runner_reports_frontend_and_runtime_phases`, `compiler_phase_errors_have_stable_javascript_messages`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
