# Commit 063: `961038ba` - l1: materialize imported scalar intrinsic implementations

| Field | Value |
|---|---|
| Commit | `961038ba06a0448461f807f6bd415d5a6b1683b0` |
| Parent reviewed | `fc437c8829f6c82c4674d54cfdb4ed4c74bf2993` |
| Author date | 2026-07-15T20:22:50-07:00 |
| Author | Pat Nakajima |
| Patch size | 19 files, +764 / -164 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 19.
- Production Rust: 12 files (+541/-65): `src/compiling/contracts.rs`, `src/compiling/core.rs`, `src/compiling/driver.rs`, `src/compiling/module.rs`, `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/compiling/typed_program/serde_test.rs`, `src/mir/generate.rs`, and 4 more.
- Tests and test oracles: 1 files (+7/-8): `tests/talk_tests.rs`.
- Language sources and benchmark fixtures: 1 files (+44/-0): `core/Operators.tlk`.
- Documentation and plans: 5 files (+172/-91): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 224 | 14 |
| `src/talk_ir/lowering.rs` | 91 | 47 |
| `src/mir/generate.rs` | 111 | 3 |
| `docs/backend-parity-plan.md` | 62 | 35 |
| `docs/backend-status.md` | 36 | 20 |
| `docs/stage-0-contract-types.md` | 34 | 11 |
| `core/Operators.tlk` | 44 | 0 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 29 | 14 |
| `src/compiling/driver.rs` | 37 | 0 |
| `src/compiling/module.rs` | 31 | 0 |
| `docs/backend-parity-ledger.md` | 11 | 11 |
| `src/compiling/contracts.rs` | 19 | 0 |
| `tests/talk_tests.rs` | 7 | 8 |
| `src/compiling/core.rs` | 11 | 0 |
| `src/compiling/typed_program/serde_test.rs` | 5 | 1 |

### Representative declarations touched

- `pub struct ScalarIntrinsicSignature {`
- `struct ScalarIntrinsicImplementation`
- `enum ScalarIntrinsicImplementationOperand`
- `pub enum TypedFunctionImplementation {`
- `impl ScalarIntrinsic {`
- `fn core_exports_audited_scalar_intrinsic_implementations`
- `fn compiles_selected_core_scalar_operators_without_external_supply`
- `impl Module {`
- `fn scalar_intrinsic_implementations`
- `impl<'a> CanonicalBuilder<'a> {`
- `impl TypedProgram {`
- `pub struct TypedFunction {`
- `fn exported_scalar_intrinsic`
- `fn valid_for`
- `fn scalar_type`
- `impl TypedProgramValidator<'_> {`
- `fn validator_rejects_malformed_exported_scalar_intrinsic_implementations`
- `fn module_interface_publishes_exact_scalar_intrinsic_implementations`
- ...and 12 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (7s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (25s): `run_rejects_offline_outside_package_execution`.
- The one full-suite failure was a `BrokenPipe` race in `run_rejects_offline_outside_package_execution`; five isolated reruns passed, so it is recorded as flaky evidence rather than a commit finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `core_exports_audited_scalar_intrinsic_implementations`, `compiles_selected_core_scalar_operators_without_external_supply`, `validator_rejects_malformed_exported_scalar_intrinsic_implementations`, `module_interface_publishes_exact_scalar_intrinsic_implementations`, `rejects_external_generic_specialization_supply`, `run_executes_audited_imported_core_scalar_operators`.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
