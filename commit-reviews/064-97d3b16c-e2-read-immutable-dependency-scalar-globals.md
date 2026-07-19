# Commit 064: `97d3b16c` - e2: read immutable dependency scalar globals

| Field | Value |
|---|---|
| Commit | `97d3b16c99d53bf24c6ccf18700b90f09d35112a` |
| Parent reviewed | `961038ba06a0448461f807f6bd415d5a6b1683b0` |
| Author date | 2026-07-15T21:41:51-07:00 |
| Author | Pat Nakajima |
| Patch size | 19 files, +799 / -129 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 19.
- Production Rust: 13 files (+676/-75): `src/compiling/contracts.rs`, `src/compiling/module.rs`, `src/compiling/package.rs`, `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`, and 5 more.
- Tests and test oracles: 1 files (+3/-7): `tests/talk_tests.rs`.
- Documentation and plans: 5 files (+120/-47): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 240 | 14 |
| `src/talk_ir/linking.rs` | 97 | 25 |
| `src/mir/generate.rs` | 92 | 7 |
| `src/compiling/typed_program/build.rs` | 63 | 13 |
| `src/compiling/package.rs` | 67 | 3 |
| `src/mir/mod.rs` | 51 | 0 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 37 | 12 |
| `docs/backend-status.md` | 31 | 13 |
| `docs/stage-0-contract-types.md` | 33 | 7 |
| `src/compiling/module.rs` | 35 | 1 |
| `docs/backend-parity-ledger.md` | 10 | 8 |
| `docs/backend-parity-plan.md` | 9 | 7 |
| `src/mir/verify.rs` | 8 | 6 |
| `src/compiling/contracts.rs` | 11 | 0 |
| `tests/talk_tests.rs` | 3 | 7 |

### Representative declarations touched

- `pub enum TypedFunctionImplementation {`
- `pub struct TypedGlobal {`
- `pub struct CallableContract {`
- `fn has_no_concrete_effects`
- `impl Module {`
- `fn imported_globals`
- `fn write_dependency_source`
- `fn reads_immutable_scalar_exports_from_a_package_dependency`
- `fn initializes_an_imported_global_before_a_consumer_global_reads_it`
- `impl<'a> CanonicalBuilder<'a> {`
- `fn create_global_reader`
- `impl TypedProgram {`
- `impl TypedItem {`
- `pub struct TypedFunction {`
- `fn is_exact_global_reader`
- `fn supports_reader_scheme`
- `impl TypedProgramValidator<'_> {`
- `fn producer_publishes_one_exact_reader_for_an_exported_immutable_scalar_global`
- ...and 15 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (6s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (26s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `reads_immutable_scalar_exports_from_a_package_dependency`, `initializes_an_imported_global_before_a_consumer_global_reads_it`, `producer_publishes_one_exact_reader_for_an_exported_immutable_scalar_global`, `rejects_external_global_places_that_bypass_generated_readers`.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
