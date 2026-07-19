# Commit 047: `813c21c8` - e2: execute scalar package graphs

| Field | Value |
|---|---|
| Commit | `813c21c8301d194b5e1f207fd6150c46eb33ed7a` |
| Parent reviewed | `fe6b86861a18a722902d147a3a8e1ba02677d806` |
| Author date | 2026-07-15T12:42:36-07:00 |
| Author | Pat Nakajima |
| Patch size | 7 files, +905 / -59 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 7.
- Production Rust: 3 files (+794/-35): `src/bin/talk.rs`, `src/compiling/driver.rs`, `src/compiling/package.rs`.
- Tests and test oracles: 1 files (+67/-0): `tests/talk_tests.rs`.
- Documentation and plans: 3 files (+44/-24): `docs/backend-parity-ledger.md`, `docs/backend-status.md`, `src/compiling/README.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/package.rs` | 668 | 3 |
| `src/bin/talk.rs` | 61 | 21 |
| `src/compiling/driver.rs` | 65 | 11 |
| `tests/talk_tests.rs` | 67 | 0 |
| `docs/backend-status.md` | 30 | 12 |
| `docs/backend-parity-ledger.md` | 9 | 9 |
| `src/compiling/README.md` | 5 | 3 |

### Representative declarations touched

- `async fn main() {`
- `pub enum ScalarCompilationError {`
- `impl std::fmt::Display for ScalarCompilationError {`
- `pub struct ScalarExecutable {`
- `struct ScalarModuleCompilation`
- `fn stable_id`
- `fn interface`
- `impl ScalarExecutable {`
- `fn link`
- `impl Driver<Typed> {`
- `fn compile_scalar_module`
- `fn lower_scalar_talk_ir`
- `fn module_artifact`
- `fn module`
- `impl PackageResolver {`
- `struct PackageBuildModuleId`
- `struct PackageBuildModule`
- `struct PackageBuildPlan`
- ...and 20 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (6s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (23s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `package_build_order_is_deterministic_and_dependency_first`, `compiles_and_executes_a_scalar_package_graph`, `compiles_a_package_library_before_its_binary`, `rejects_invalid_package_supply_before_compilation`, `rejects_missing_and_ambiguous_package_entries`, `package_build_fails_closed_for_unsupported_source_forms`, `run_executes_a_locked_scalar_package_graph`.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
