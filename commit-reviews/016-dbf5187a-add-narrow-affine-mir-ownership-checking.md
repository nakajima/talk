# Commit 016: `dbf5187a` - add narrow affine MIR ownership checking

| Field | Value |
|---|---|
| Commit | `dbf5187ae4b1f3860c7c2704f1feafe1a07876d8` |
| Parent reviewed | `1e22b4c727b70033a9922f4724d7150355d51a8a` |
| Author date | 2026-07-14T11:47:20-07:00 |
| Author | Pat Nakajima |
| Patch size | 6 files, +2493 / -222 |
| Review result | **Standalone defect, repaired later** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 6.
- Production Rust: 4 files (+2459/-204): `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`.
- Documentation and plans: 2 files (+34/-18): `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/generate.rs` | 1151 | 98 |
| `src/mir/verify.rs` | 969 | 105 |
| `src/compiling/typed_program/contract.rs` | 327 | 1 |
| `docs/backend-status.md` | 33 | 18 |
| `src/mir/mod.rs` | 12 | 0 |
| `docs/stage-0-contract-types.md` | 1 | 0 |

### Representative declarations touched

- `pub enum OwnershipDiagnosticKind {`
- `struct AffineFixtures`
- `fn origin`
- `fn resource_symbol`
- `fn resource_ty`
- `fn binding`
- `fn parameter`
- `fn value`
- `fn local_value`
- `fn destination`
- `fn function`
- `fn program`
- `fn program_with_grade`
- `fn move_into_local`
- `fn generic_copy_storage_main`
- `fn custom_copy_cleanup_main`
- `fn affine_cleanup_main`
- `fn affine_move_return_main`
- ...and 83 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (11s): `talk_ir::lowering::tests::adapts_parameters_before_a_mir_entry_with_a_backedge`, `talk_ir::lowering::tests::lowers_generated_local_storage`, `talk_ir::lowering::tests::lowers_verified_external_call_fixture`, `talk_ir::lowering::tests::lowers_verified_local_direct_call_fixture`, `talk_ir::lowering::tests::lowers_verified_local_storage_and_multiple_blocks_fixture`, `talk_ir::lowering::tests::rejects_intrinsics_without_a_target_neutral_mapping`.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `generates_affine_move_cleanup_and_assignment_ordering`, `generates_affine_drop_flags_only_for_cfg_joins`, `reports_affine_source_ownership_errors`, `cleans_affine_values_on_early_return`.
- No test files or executable language test fixtures changed in this patch.

## Findings

### 1. [P1] Update checked-MIR lowering fixtures in the same commit as the new cleanup invariant

- Location: `src/mir/mod.rs` and `src/talk_ir/lowering.rs` tests
- Status: **Fixed later by `b73ad318`**
- Impact: The new affine ownership verifier immediately invalidates six existing Talk IR lowering fixtures. Five panic with `IncompleteCleanup` for local 0 and one observes an extra generated block. The production code compiles, but the commit leaves the default test suite red; the next two verifier hardening commits inherit the same failures until `b73ad318` updates the fixtures.
- Evidence: `cargo test --locked` fails at this exact commit: 852 passed, 6 failed, 3 ignored; the representative entry-backedge test failed twice in isolated reruns.
- Recommended correction: Land the cleanup-aware fixture construction and updated block expectation from `b73ad318` with the verifier that makes them mandatory.

## Disposition

Do not use this as an independently mergeable/bisectable commit. The cited later commit repairs the defect, but the history should ideally be squashed or reordered so every retained commit is green.
