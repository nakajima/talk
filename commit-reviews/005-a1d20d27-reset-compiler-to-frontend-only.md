# Commit 005: `a1d20d27` - reset compiler to frontend-only

| Field | Value |
|---|---|
| Commit | `a1d20d27fd25db78005c90759993bfb85641424e` |
| Parent reviewed | `96249e71127bacf16060afd9d12435deb871f76c` |
| Author date | 2026-07-13T17:33:53-07:00 |
| Author | Pat Nakajima |
| Patch size | 103 files, +398 / -43468 |
| Review result | **Request changes** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 1, D: 60, M: 42.
- Production Rust: 63 files (+154/-29924): `src/analysis/hover.rs`, `src/analysis/mod.rs`, `src/analysis/ownership.rs`, `src/analysis/workspace.rs`, `src/bin/talk.rs`, `src/common/diagnostic.rs`, `src/compiling/core.rs`, `src/compiling/driver.rs`, and 55 more.
- Tests and test oracles: 14 files (+3/-11161): `benches/vm_e2e.rs`, `src/flow/flow_borrow_tests.rs`, `src/flow/flow_tests.rs`, `src/lambda_g/balance_tests.rs`, `src/lambda_g/lambda_g_tests.rs`, `src/lower/lower_tests.rs`, `src/types/types_tests.rs`, `src/vm/vm_tests.rs`, and 6 more.
- Language sources and benchmark fixtures: 1 files (+0/-61): `examples/_pi_spinup.rs`.
- Build, packaging, and CI: 2 files (+0/-233): `Cargo.lock`, `Cargo.toml`.
- Documentation and plans: 22 files (+237/-2089): `docs/adr/0008-managed-storage-and-ffi.md`, `docs/adr/0009-standalone-executables-via-bundled-vm.md`, `docs/adr/0010-flow-analysis-on-the-mir-cfg.md`, `docs/adr/0011-dynamic-extent-effect-handlers.md`, `docs/adr/0015-typing-publishes-lowering-reads.md`, `docs/adr/0017-structural-temp-drops-and-free-balance-verifier.md`, `docs/adr/0019-typed-program-to-checked-mir.md`, `docs/adr/0027-effect-abort-unwinding.md`, and 14 more.
- Other: 1 files (+4/-0): `talk-c/include/talk_c.h`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/lower/mir.rs` | 0 | 4284 |
| `src/vm/vm_tests.rs` | 0 | 3462 |
| `src/flow/flow_tests.rs` | 0 | 2187 |
| `src/flow/moves.rs` | 0 | 1989 |
| `src/lower/mir_lowering.rs` | 0 | 1810 |
| `tests/fuzz.rs` | 0 | 1528 |
| `src/lambda_g/eval.rs` | 0 | 1447 |
| `src/lambda_g/balance.rs` | 0 | 1356 |
| `src/flow/flow_borrow_tests.rs` | 0 | 1186 |
| `src/vm/schedule.rs` | 0 | 1173 |
| `src/lower/patterns.rs` | 0 | 1172 |
| `src/lower/mod.rs` | 0 | 1168 |
| `src/lower/statements.rs` | 0 | 1143 |
| `src/flow/cfg.rs` | 0 | 1086 |
| `src/flow/loans.rs` | 0 | 1050 |

### Representative declarations touched

- `fn hover_for_node(workspace: &Workspace, node: &Node) -> Option<Hover> {`
- `fn hover_for_symbol(`
- `pub enum DiagnosticKind {`
- `impl DiagnosticKind {`
- `pub struct Workspace {`
- `impl Workspace {`
- `pub(crate) fn diagnostic_for_any(`
- `async fn main() {`
- `impl Downloader {`
- `fn update_current_package(`
- `pub enum AnyDiagnostic {`
- `impl From<Diagnostic<TypeError>> for AnyDiagnostic {`
- `impl fmt::Display for AnyDiagnostic {`
- `pub fn path_override() -> Option<PathBuf> {`
- `fn compilation_sources() -> Vec<Source> {`
- `fn _compile`
- `fn _compile() -> (Arc<Module>, Arc<LibraryTyped>) {`
- `pub struct NameResolved {`
- ...and 41 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (5s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (14s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `execution_compatibility_entries_report_frontend_only_errors`.
- Existing test surfaces changed: `benches/vm_e2e.rs`, `src/flow/flow_borrow_tests.rs`, `src/flow/flow_tests.rs`, `src/lambda_g/balance_tests.rs`, `src/lambda_g/lambda_g_tests.rs`, `src/lower/lower_tests.rs`, `src/types/types_tests.rs`, `src/vm/vm_tests.rs`, `talk-swift/Tests/TalkSwiftTests/TalkSwiftTests.swift`, `tests/examples.rs`, `tests/fuzz.rs`, `tests/programs.rs` and 2 more.

## Findings

### 1. [P1] Remove or replace the CI fuzz step when deleting its target

- Location: `.github/workflows/ci.yml:27-28`, `Cargo.toml`, and deleted `tests/fuzz.rs`
- Status: **Unresolved at branch tip**
- Impact: This reset deletes the `fuzz-tests` feature and the `tests/fuzz.rs` integration target, but leaves the CI command `cargo test --test fuzz --features fuzz-tests --verbose --locked` in place. GitHub Actions therefore exits before running a fuzz test with `the package talk does not contain this feature: fuzz-tests`. The stale documentation in `docs/ownership-soundness-plan.md` and `docs/single-source-of-truth-plan.md` also still says that this target is present and required.
- Evidence: `cargo test --test fuzz --features fuzz-tests --locked` fails immediately on the branch tip.
- Recommended correction: Either restore a maintained fuzz target and feature, or remove the CI step and update the plans in the same reset commit.

## Disposition

Do not merge this commit as currently represented at the branch tip until the unresolved finding above is corrected.
