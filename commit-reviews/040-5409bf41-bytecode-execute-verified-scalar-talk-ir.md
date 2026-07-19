# Commit 040: `5409bf41` - bytecode: execute verified scalar talk ir

| Field | Value |
|---|---|
| Commit | `5409bf41eebee1ea71a90e361c2ae7e9733ab17d` |
| Parent reviewed | `872ba1eac04ee837e9ed283c4b614a3bfddfa26e` |
| Author date | 2026-07-15T01:24:13-07:00 |
| Author | Pat Nakajima |
| Patch size | 12 files, +1557 / -54 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 1, M: 11.
- Production Rust: 3 files (+1440/-0): `src/bytecode/mod.rs`, `src/lib.rs`, `src/talk_ir/mod.rs`.
- Build, packaging, and CI: 2 files (+3/-0): `Cargo.lock`, `Cargo.toml`.
- Documentation and plans: 7 files (+114/-54): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/e1-talk-runtime-reuse-audit.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/bytecode/mod.rs` | 1244 | 0 |
| `src/talk_ir/mod.rs` | 195 | 0 |
| `docs/backend-status.md` | 35 | 18 |
| `docs/e1-talk-runtime-reuse-audit.md` | 14 | 14 |
| `docs/backend-parity-ledger.md` | 13 | 13 |
| `docs/stage-0-contract-types.md` | 23 | 0 |
| `docs/e1-scalar-execution-plan.md` | 13 | 6 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 13 | 0 |
| `docs/backend-parity-plan.md` | 3 | 3 |
| `Cargo.toml` | 2 | 0 |
| `src/lib.rs` | 1 | 0 |
| `Cargo.lock` | 1 | 0 |

### Representative declarations touched

- `fn compile`
- `enum BytecodeLoweringError`
- `fn fmt`
- `fn source`
- `fn preflight`
- `fn preflight_function`
- `fn preflight_instruction`
- `fn preflight_terminator`
- `fn is_e1_value_type`
- `fn kind_name`
- `fn unsupported`
- `fn invalid`
- `struct Pools`
- `fn constant`
- `fn arguments`
- `fn trap`
- `fn e1_constant`
- `struct Registers`
- ...and 35 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (8s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (26s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `compiles_and_executes_verified_constant_talk_ir`, `executes_source_slots_branch_and_direct_call`, `executes_source_switch_recursive_cfg_and_unit_return`, `executes_source_scalar_operations_and_reports_clean_traps`, `executes_parallel_edge_copy_cycles_with_a_temporary_register`, `rejects_talk_ir_outside_the_e1_target_profile_before_emission`, `maps_every_scalar_intrinsic_to_the_audited_profile`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
