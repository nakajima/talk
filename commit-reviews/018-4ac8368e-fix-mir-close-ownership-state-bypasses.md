# Commit 018: `4ac8368e` - fix(mir): close ownership state bypasses

| Field | Value |
|---|---|
| Commit | `4ac8368ea2875766a7ec8b160df0c8b38fc60dd9` |
| Parent reviewed | `266ba1556782c4d7173563f460bf714f0c089848` |
| Author date | 2026-07-14T13:58:34-07:00 |
| Author | Pat Nakajima |
| Patch size | 7 files, +245 / -18 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 7.
- Production Rust: 4 files (+224/-10): `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`.
- Documentation and plans: 3 files (+21/-8): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/mod.rs` | 105 | 3 |
| `src/mir/verify.rs` | 41 | 7 |
| `src/mir/generate.rs` | 44 | 0 |
| `src/compiling/typed_program/contract.rs` | 34 | 0 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 10 | 5 |
| `docs/backend-status.md` | 8 | 2 |
| `docs/stage-0-contract-types.md` | 3 | 1 |

### Representative declarations touched

- `fn affine_discarded_node_expression_main`
- `fn affine_discarded_statement_expression_main`
- `impl<'program> FunctionGenerator<'program> {`
- `fn rejects_discarded_affine_expression_values_before_lowering`
- `fn immutable_reinitialization_candidate`
- `fn immutable_call_reinitialization_candidate`
- `fn rejects_reinitialization_of_immutable_storage_after_discard`
- `fn rejects_call_reinitialization_of_immutable_storage_after_discard`
- `impl<'mir> MirVerifier<'mir> {`
- `struct AffineSlot {`
- `impl AffineFlowState {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (3s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (7s): `talk_ir::lowering::tests::adapts_parameters_before_a_mir_entry_with_a_backedge`, `talk_ir::lowering::tests::lowers_generated_local_storage`, `talk_ir::lowering::tests::lowers_verified_external_call_fixture`, `talk_ir::lowering::tests::lowers_verified_local_direct_call_fixture`, `talk_ir::lowering::tests::lowers_verified_local_storage_and_multiple_blocks_fixture`, `talk_ir::lowering::tests::rejects_intrinsics_without_a_target_neutral_mapping`.
- This test failure is inherited from `dbf5187a`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `rejects_discarded_affine_expression_values_before_lowering`, `rejects_reinitialization_of_immutable_storage_after_discard`, `rejects_call_reinitialization_of_immutable_storage_after_discard`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `dbf5187a`. Correct or squash the originating commit before retaining this point in history.
