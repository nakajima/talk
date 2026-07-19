# Commit 009: `bdb74959` - generate verified Copy-only MIR CFGs

| Field | Value |
|---|---|
| Commit | `bdb749595df42c0d876f73a1e0d950d0f5f7a1e7` |
| Parent reviewed | `7b876a65b3acf99902ef3b169687507ca8f92267` |
| Author date | 2026-07-14T00:47:28-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +3151 / -380 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 2, M: 2.
- Production Rust: 4 files (+3151/-380): `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/generate.rs` | 1398 | 0 |
| `src/mir/verify.rs` | 1293 | 0 |
| `src/mir/mod.rs` | 183 | 326 |
| `src/compiling/typed_program/contract.rs` | 277 | 54 |

### Representative declarations touched

- `struct CopyFixtures`
- `fn origin`
- `fn int_ty`
- `fn contract`
- `fn int`
- `fn bool`
- `fn block`
- `fn function`
- `fn return_value`
- `fn program`
- `fn copy_binding_main`
- `fn uninitialized_copy_main`
- `fn copy_branch_main`
- `fn copy_loop_main`
- `fn copy_switch_main`
- `fn copy_direct_call_main`
- `enum MirGenerationDiagnostic`
- `fn from_invariant`
- ...and 96 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (11s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `only_current_module_items_are_exported`, `generates_copy_only_return_from_validated_typed_program`, `reports_uninitialized_reads_as_source_diagnostics`, `generates_explicit_copy_local_operations`, `generates_copy_only_cfg_terminators`, `rejects_an_invalid_entry_block`, `checks_copy_only_semantics`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
