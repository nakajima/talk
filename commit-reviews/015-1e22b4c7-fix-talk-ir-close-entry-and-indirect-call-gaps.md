# Commit 015: `1e22b4c7` - fix(talk-ir): close entry and indirect call gaps

| Field | Value |
|---|---|
| Commit | `1e22b4c727b70033a9922f4724d7150355d51a8a` |
| Parent reviewed | `7ecba6b3d600906ab71b01f95f9c398573925a15` |
| Author date | 2026-07-14T14:05:06-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +198 / -15 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 4.
- Production Rust: 3 files (+196/-14): `src/mir/mod.rs`, `src/talk_ir/lowering.rs`, `src/talk_ir/mod.rs`.
- Documentation and plans: 1 files (+2/-1): `docs/backend-status.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/talk_ir/lowering.rs` | 67 | 14 |
| `src/mir/mod.rs` | 77 | 0 |
| `src/talk_ir/mod.rs` | 52 | 0 |
| `docs/backend-status.md` | 2 | 1 |

### Representative declarations touched

- `fn copy_parameter_entry_backedge`
- `struct FunctionLowerer<'lowerer, 'mir> {`
- `impl<'lowerer, 'mir> FunctionLowerer<'lowerer, 'mir> {`
- `fn lower_entry_adapter`
- `fn adapts_parameters_before_a_mir_entry_with_a_backedge`
- `impl<'ir> TalkIrVerifier<'ir> {`
- `fn indirect_non_function_call_candidate`
- `fn verifier_rejects_indirect_calls_fail_closed`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (7s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `adapts_parameters_before_a_mir_entry_with_a_backedge`, `verifier_rejects_indirect_calls_fail_closed`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
