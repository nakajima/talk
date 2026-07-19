# Commit 041: `17700926` - cli: run validated scalar bytecode

| Field | Value |
|---|---|
| Commit | `17700926cab27a4b754d328cf92626e1db4de1c0` |
| Parent reviewed | `5409bf41eebee1ea71a90e361c2ae7e9733ab17d` |
| Author date | 2026-07-15T01:40:18-07:00 |
| Author | Pat Nakajima |
| Patch size | 14 files, +541 / -34 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 2, M: 12.
- Production Rust: 3 files (+344/-0): `src/bin/talk.rs`, `src/compiling/driver.rs`, `talk-runtime/src/scalar.rs`.
- Tests and test oracles: 2 files (+120/-0): `tests/parity/reviewed-programs/handlers.stdout`, `tests/talk_tests.rs`.
- Documentation and plans: 9 files (+77/-34): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/e1-talk-runtime-reuse-audit.md`, `docs/stage-0-contract-types.md`, `tests/parity/programs/README.md`, and 1 more.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/driver.rs` | 256 | 0 |
| `tests/talk_tests.rs` | 117 | 0 |
| `src/bin/talk.rs` | 50 | 0 |
| `talk-runtime/src/scalar.rs` | 38 | 0 |
| `docs/backend-status.md` | 21 | 11 |
| `docs/backend-parity-ledger.md` | 10 | 12 |
| `tests/parity/programs/README.md` | 6 | 4 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 10 | 0 |
| `docs/stage-0-contract-types.md` | 9 | 0 |
| `docs/e1-scalar-execution-plan.md` | 6 | 3 |
| `tests/parity/reviewed-programs/README.md` | 8 | 0 |
| `docs/backend-parity-plan.md` | 3 | 3 |
| `docs/e1-talk-runtime-reuse-audit.md` | 4 | 1 |
| `tests/parity/reviewed-programs/handlers.stdout` | 3 | 0 |

### Representative declarations touched

- `async fn main() {`
- `pub struct Typed {`
- `enum ScalarCompilationError`
- `fn fmt`
- `struct ScalarExecutable`
- `struct ScalarExecution`
- `fn rendered`
- `fn render_bytecode`
- `fn run`
- `impl Driver<Typed> {`
- `fn compile_scalar`
- `fn select_scalar_entry`
- `fn typed_scalar_source`
- `fn compiles_and_runs_the_scalar_pipeline_with_talk_result_rendering`
- `fn scalar_pipeline_suppresses_unit_and_selects_explicit_exports`
- `fn scalar_pipeline_rejects_ambiguous_or_missing_entries`
- `impl ValidatedBytecodeModule {`
- `fn render_result`
- ...and 10 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (5s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (23s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `compiles_and_runs_the_scalar_pipeline_with_talk_result_rendering`, `scalar_pipeline_suppresses_unit_and_selects_explicit_exports`, `scalar_pipeline_rejects_ambiguous_or_missing_entries`, `renders_results_with_talk_syntax_and_suppresses_unit`, `run_source`, `run_executes_validated_scalar_source_with_talk_rendering`, `run_prefers_the_source_entrypoint_without_an_explicit_export`, `run_selects_an_explicit_zero_parameter_export`, `run_suppresses_unit_and_reports_clean_scalar_traps`, `run_rejects_unsupported_operator_lowering_without_backend_fallback`, `reviewed_handlers_oracle_uses_talk_result_rendering`.
- Added Talk/expected-output fixtures: `tests/parity/reviewed-programs/handlers.stdout`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
