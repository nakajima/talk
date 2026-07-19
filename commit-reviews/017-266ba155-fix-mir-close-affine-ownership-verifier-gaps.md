# Commit 017: `266ba155` - fix(mir): close affine ownership verifier gaps

| Field | Value |
|---|---|
| Commit | `266ba1556782c4d7173563f460bf714f0c089848` |
| Parent reviewed | `dbf5187ae4b1f3860c7c2704f1feafe1a07876d8` |
| Author date | 2026-07-14T13:30:55-07:00 |
| Author | Pat Nakajima |
| Patch size | 7 files, +874 / -634 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 7.
- Production Rust: 4 files (+839/-622): `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`.
- Documentation and plans: 3 files (+35/-12): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/verify.rs` | 168 | 564 |
| `src/mir/mod.rs` | 346 | 3 |
| `src/mir/generate.rs` | 177 | 39 |
| `src/compiling/typed_program/contract.rs` | 148 | 16 |
| `docs/backend-status.md` | 19 | 8 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 12 | 3 |
| `docs/stage-0-contract-types.md` | 4 | 1 |

### Representative declarations touched

- `pub enum BorrowEventKind {`
- `fn origin_at`
- `fn affine_block_local_transfer_main`
- `fn affine_call_with_later_call_argument_main`
- `impl<'program> FunctionGenerator<'program> {`
- `fn owner_event`
- `fn ownership_event`
- `fn rejects_block_local_affine_transfer_as_an_implementation_gap`
- `fn rejects_affine_call_arguments_before_a_later_cfg_argument`
- `fn reports_affine_source_ownership_errors_with_causative_origins`
- `impl BorrowEvent {`
- `pub struct OwnershipDiagnostic {`
- `struct AffineMain`
- `fn resource_item`
- `fn resource_ty`
- `fn place`
- `fn contract`
- `fn candidate`
- ...and 17 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (10s): `talk_ir::lowering::tests::adapts_parameters_before_a_mir_entry_with_a_backedge`, `talk_ir::lowering::tests::lowers_generated_local_storage`, `talk_ir::lowering::tests::lowers_verified_external_call_fixture`, `talk_ir::lowering::tests::lowers_verified_local_direct_call_fixture`, `talk_ir::lowering::tests::lowers_verified_local_storage_and_multiple_blocks_fixture`, `talk_ir::lowering::tests::rejects_intrinsics_without_a_target_neutral_mapping`.
- This test failure is inherited from `dbf5187a`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `rejects_affine_call_arguments_before_a_later_cfg_argument`, `reports_affine_source_ownership_errors_with_causative_origins`, `accepts_correlated_affine_drop_flags`, `rejects_out_of_range_destroy_if_live_flags`, `rejects_destroy_if_live_flags_for_the_wrong_place`, `rejects_missing_predecessor_drop_flag_updates`, `rejects_incorrect_predecessor_drop_flag_updates`, `rejects_replacement_of_canonically_immutable_storage`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `dbf5187a`. Correct or squash the originating commit before retaining this point in history.
