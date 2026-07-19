# Commit 053: `0a968e67` - merge: integrate lane B local specialization

| Field | Value |
|---|---|
| Commit | `0a968e6728264eaeaaa1bbbc8c5035dfbde3c33f` |
| Parent reviewed | `88618ddd3a72aad7373960093fcdfb0fbcf35833` |
| Other parents | `79086d6e1cf6e8b8d46d43f2f9a357232586895b` |
| Author date | 2026-07-15T18:27:36-07:00 |
| Author | Pat Nakajima |
| Patch size | 9 files, +1648 / -209 |
| Review result | **Standalone defect, repaired later** |

## Intent and sequence context

# Conflicts:
#	docs/backend-parity-ledger.md

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 9.
- Production Rust: 6 files (+1557/-191): `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`, `src/talk_ir/lowering.rs`.
- Tests and test oracles: 1 files (+31/-1): `tests/talk_tests.rs`.
- Documentation and plans: 2 files (+60/-17): `docs/backend-parity-ledger.md`, `docs/backend-status.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/talk_ir/lowering.rs` | 663 | 123 |
| `src/compiling/typed_program/contract.rs` | 284 | 0 |
| `src/mir/verify.rs` | 224 | 42 |
| `src/mir/generate.rs` | 208 | 18 |
| `src/mir/mod.rs` | 121 | 1 |
| `docs/backend-status.md` | 54 | 11 |
| `src/compiling/typed_program/build.rs` | 57 | 7 |
| `tests/talk_tests.rs` | 31 | 1 |
| `docs/backend-parity-ledger.md` | 6 | 6 |

### Representative declarations touched

- `impl<'a> CanonicalBuilder<'a> {`
- `fn canonical_call_instantiation`
- `impl TypedProgramValidator<'_> {`
- `fn callable_function_instantiation`
- `fn generic_instantiation_program`
- `fn generic_instantiation_mut`
- `fn monomorphic_instantiation_program`
- `fn monomorphic_instantiation_mut`
- `fn assert_invalid_generic_instantiation`
- `fn validator_rejects_unexpected_monomorphic_instantiation_mapping`
- `fn validator_rejects_missing_generic_instantiation_mapping`
- `fn validator_rejects_duplicate_generic_instantiation_mapping`
- `fn validator_rejects_unknown_generic_instantiation_mapping`
- `fn validator_rejects_reordered_generic_instantiation_mapping`
- `fn producer_publishes_complete_ordered_recursive_generic_instantiations`
- `impl<'program> FunctionGenerator<'program> {`
- `fn preserves_complete_generic_and_recursive_call_instantiations`
- `fn rejects_protocol_defaults_without_a_frontend_selected_implementation`
- ...and 36 additional declaration contexts.

## Test and validation review

- Historical checkout compilation was not repeated because this patch changes only documentation/language fixtures/oracles and no Rust or Cargo inputs.
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (16s): `compiling::package::tests::package_build_fails_closed_for_unsupported_source_forms`.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `validator_rejects_unexpected_monomorphic_instantiation_mapping`, `validator_rejects_missing_generic_instantiation_mapping`, `validator_rejects_duplicate_generic_instantiation_mapping`, `validator_rejects_unknown_generic_instantiation_mapping`, `validator_rejects_reordered_generic_instantiation_mapping`, `producer_publishes_complete_ordered_recursive_generic_instantiations`, `preserves_complete_generic_and_recursive_call_instantiations`, `rejects_protocol_defaults_without_a_frontend_selected_implementation`, `verifies_generic_call_arity_and_concreteness`, `rejects_a_mismatched_selected_implementation`, `specializes_generic_scalar_calls_once_per_canonical_key`, `preallocates_recursive_generic_specializations_and_executes_them`, `materializes_exact_frontend_selected_local_implementations`, `rejects_external_selected_implementation_specialization_supply`, `run_executes_local_generic_scalar_specializations`.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

### 1. [P1] Update the package fail-closed test when the merge makes generic packages executable

- Location: `src/compiling/package.rs::package_build_fails_closed_for_unsupported_source_forms`
- Status: **Fixed later by `0a9ead59`**
- Impact: Lane B makes the generic package fixture compile successfully, but the first-parent merge keeps a test that requires that fixture to fail closed. The merge therefore has a deterministic default-suite failure, inherited by the lane-C merge and the following documentation commit. `0a9ead59` later splits the now-supported generic case into a positive integration test and keeps an actually unsupported aggregate fixture as the negative case.
- Evidence: `cargo test --locked` fails 960 passed / 1 failed / 3 ignored at this merge; the isolated package test failed twice.
- Recommended correction: Include the package-test disposition from `0a9ead59` in this merge resolution so the integrated behavior and oracle change atomically.

## Disposition

Do not use this as an independently mergeable/bisectable commit. The cited later commit repairs the defect, but the history should ideally be squashed or reordered so every retained commit is green.
