# Commit 014: `7ecba6b3` - lower verified MIR forms to Talk IR

| Field | Value |
|---|---|
| Commit | `7ecba6b3d600906ab71b01f95f9c398573925a15` |
| Parent reviewed | `74b9fc9ea7700b19ffae03c00b212c6f480e4044` |
| Author date | 2026-07-14T11:30:38-07:00 |
| Author | Pat Nakajima |
| Patch size | 5 files, +2057 / -207 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 5.
- Production Rust: 3 files (+2017/-176): `src/mir/mod.rs`, `src/talk_ir/lowering.rs`, `src/talk_ir/mod.rs`.
- Documentation and plans: 2 files (+40/-31): `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/talk_ir/lowering.rs` | 974 | 152 |
| `src/talk_ir/mod.rs` | 625 | 21 |
| `src/mir/mod.rs` | 418 | 3 |
| `docs/backend-status.md` | 39 | 30 |
| `docs/stage-0-contract-types.md` | 1 | 1 |

### Representative declarations touched

- `pub struct IrImport {`
- `fn contract_with_inputs`
- `fn parameter`
- `fn int_ty`
- `fn bool_ty`
- `fn place`
- `fn constant`
- `fn int`
- `fn boolean`
- `fn copy`
- `fn callable`
- `fn copy_local_blocks`
- `fn copy_cfg`
- `fn copy_local_call`
- `fn copy_external_call`
- `fn copy_intrinsic_call`
- `fn nonlocal_call`
- `impl fmt::Display for LoweringError {`
- ...and 61 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (3s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (9s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `lowers_generated_copy_only_mir`, `lowers_verified_local_storage_and_multiple_blocks_fixture`, `lowers_generated_local_storage`, `lowers_verified_copy_cfg_fixture`, `lowers_generated_copy_cfg`, `lowers_verified_local_direct_call_fixture`, `lowers_generated_local_direct_call`, `lowers_verified_external_call_fixture`, `lowers_generated_external_call`, `rejects_intrinsics_without_a_target_neutral_mapping`, `verifier_rejects_a_store_with_the_wrong_value_type`, `verifier_rejects_a_non_boolean_branch_condition`, `verifier_checks_local_direct_call_arguments`, `verifier_checks_external_import_call_arguments`, `verifier_rejects_an_empty_import_export_name`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
