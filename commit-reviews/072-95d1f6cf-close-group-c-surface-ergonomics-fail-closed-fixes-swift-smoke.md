# Commit 072: `95d1f6cf` - Close group C: surface ergonomics, fail-closed fixes, Swift smoke

| Field | Value |
|---|---|
| Commit | `95d1f6cf052acbbf7c95ee09d1796df0b5edc31d` |
| Parent reviewed | `5329de53d541ed0f686a2f5225b718de5a0b9b9a` |
| Author date | 2026-07-16T10:10:57-07:00 |
| Author | Pat Nakajima |
| Patch size | 7 files, +586 / -85 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

- Character literals compile to borrowed grapheme views over immortal
  static bytes (the string-literal statics mechanism).
- Or-pattern alternatives share one local per bound name.
- `mut` arguments: the receiver writeback convention generalizes to all
  exclusive-borrow parameters — callee returns (result, final values…)
  in declaration order, caller writes each back to its place (local or
  global slot). `mut` parameters on function values fail closed.
- Nested `func` declarations index like top-level ones, so calls to
  them — including self-recursion — resolve; capturing ones keep their
  CHG-06 rejection.
- Two silent misbehaviors now fail closed: assignment to a captured
  value (wrote the environment copy) and user handlers over ambient
  core effects (bypassed by the runtime's implicit handler).
- CHG-01 clause-perform routing pinned by a black-box test.
- talk-c: package test, lowered render, bytecode render, and bytecode
  compile execute through the backend instead of frontend-only stubs.
- talk-swift: added Package.swift; the XCTest suite runs program
  execution, package run/test, and diagnostics through the C ABI.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 1, M: 6.
- Production Rust: 2 files (+427/-75): `src/backend/mir.rs`, `talk-c/src/lib.rs`.
- Tests and test oracles: 2 files (+89/-4): `talk-swift/Tests/TalkSwiftTests/TalkSwiftTests.swift`, `tests/talk_tests.rs`.
- Build, packaging, and CI: 1 files (+17/-0): `talk-swift/Package.swift`.
- Documentation and plans: 2 files (+53/-6): `docs/backend-parity-ledger.md`, `docs/lean-rebuild-wave-reports.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 302 | 54 |
| `talk-c/src/lib.rs` | 125 | 21 |
| `tests/talk_tests.rs` | 73 | 1 |
| `docs/lean-rebuild-wave-reports.md` | 40 | 0 |
| `talk-swift/Tests/TalkSwiftTests/TalkSwiftTests.swift` | 16 | 3 |
| `docs/backend-parity-ledger.md` | 13 | 6 |
| `talk-swift/Package.swift` | 17 | 0 |

### Representative declarations touched

- `fn free_locals(`
- `fn pattern_bind_symbols`
- `fn walk`
- `impl<'a> ProgramBuilder<'a> {`
- `fn index_nested_funcs`
- `fn index_nested_stmt`
- `fn index_nested_expr`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `impl TalkResult {`
- `fn ok_bytes`
- `impl ProgramRunner {`
- `fn typed`
- `impl PackageRunner {`
- `pub extern "C" fn talk_render_lowered_utf8(`
- `pub extern "C" fn talk_render_bytecode_utf8(`
- `pub extern "C" fn talk_compile_bytecode_utf8(`
- `fn buffer_string`
- ...and 12 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (11s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `inspection_entries_render_lowered_and_bytecode_output`, `inlay_hints_stay_unavailable`, `run_executes_mut_arguments`, `run_executes_or_pattern_bindings`, `run_executes_character_literals`, `run_executes_recursive_local_functions`, `run_routes_clause_performs_to_outer_handlers`, `run_rejects_assignment_to_captured_values`, `run_rejects_user_handlers_over_ambient_effects`.
- Existing test surfaces changed: `talk-swift/Tests/TalkSwiftTests/TalkSwiftTests.swift`, `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 925 workspace tests + 4 Swift tests pass; total <=11,741 of the

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
