# Commit 069: `ee03e896` - Rebuild the backend lean: one seam, full corpus parity

| Field | Value |
|---|---|
| Commit | `ee03e8960def53c690e586e589e96933d265588d` |
| Parent reviewed | `65c93acf18e684f448cdab2a0b25c79eba135a3d` |
| Author date | 2026-07-16T08:37:25-07:00 |
| Author | Pat Nakajima |
| Patch size | 87 files, +12450 / -39571 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Execute docs/lean-backend-rebuild-plan.md end to end. Reset the
experimental rewrite to the a1d20d27 frontend (keeping parity assets and
the LIT-01 signed-literal validation), then restore every required
behavior through one compile/execute seam per ADR 0034:

- src/backend: MIR over the typed tree with structural ownership
  (scope/temp/replacement/path-sensitive drops, use-after-move
  rejection), whole-program monomorphization, conformance-witness
  dereferencing, and bytecode lowering onto the reused talk-runtime.
- Managed strings, collections, CoW, graphemes, and 'heap regions run
  from core Talk source over the memory intrinsics; program globals are
  once-initialized static slots (LINK-02) with guarded teardown.
- Deep one-shot effects: a frame-tied runtime handler stack (4 new
  instructions) for dynamic nearest-handler routing; resume-as-return,
  structural Discontinue over the ADR 0027 unwind with per-call cleanup.
- Tools through the same path: talk run (script/entry/package), talk
  test (ported harness, JSON), build/run-image/bytecode with validation
  at the untrusted-bytes seam, REPL, talk-c, wasm, talk-static.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 6, D: 19, M: 62.
- Production Rust: 73 files (+11160/-38240): `src/analysis/completion.rs`, `src/analysis/definition.rs`, `src/analysis/hover.rs`, `src/analysis/rename.rs`, `src/analysis/workspace.rs`, `src/backend/lower.rs`, `src/backend/mir.rs`, `src/backend/mod.rs`, and 65 more.
- Tests and test oracles: 3 files (+807/-488): `src/typed_ast/typed_ast_tests.rs`, `src/types/types_tests.rs`, `tests/talk_tests.rs`.
- Language sources and benchmark fixtures: 2 files (+0/-51): `core/Iterable.tlk`, `core/Operators.tlk`.
- Build, packaging, and CI: 2 files (+0/-2): `Cargo.lock`, `wasm/Cargo.toml`.
- Documentation and plans: 5 files (+429/-789): `docs/adr/0034-lean-bytecode-backend-architecture.md`, `docs/backend-parity-ledger.md`, `docs/backend-status.md`, `docs/lean-rebuild-wave-reports.md`, `src/compiling/README.md`.
- Other: 2 files (+54/-1): `scripts/size_report.sh`, `talk-c/include/talk_c.h`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 0 | 6968 |
| `src/backend/mir.rs` | 4320 | 0 |
| `src/mir/generate.rs` | 0 | 3954 |
| `src/compiling/typed_program/build.rs` | 57 | 3493 |
| `src/mir/verify.rs` | 0 | 2790 |
| `src/mir/mod.rs` | 0 | 2597 |
| `src/talk_ir/mod.rs` | 0 | 2564 |
| `src/talk_ir/lowering.rs` | 0 | 2336 |
| `src/bytecode/mod.rs` | 0 | 1456 |
| `src/compiling/package.rs` | 225 | 1023 |
| `src/talk_ir/linking.rs` | 0 | 1110 |
| `src/mir/provenance/context.rs` | 0 | 1020 |
| `talk-runtime/src/scalar.rs` | 0 | 1017 |
| `src/analysis/rename.rs` | 908 | 46 |
| `src/lsp/rename.rs` | 931 | 16 |

### Representative declarations touched

- `enum surface`
- `pub struct CompletionAnalysis<'a> {`
- `pub fn complete_in_workspace(`
- `pub fn complete(`
- `fn member_completion_dot(text: &str, byte_offset: u32) -> Option<u32> {`
- `fn is_ident_byte`
- `fn member_completions(analysis: &CompletionAnalysis<'_>, dot_offset: u32) -> Vec`
- `fn member_completion_receiver(ast: &AST<NameResolved>, dot_offset: u32) -> Optio`
- `fn type_receiver_symbol`
- `fn add_member_items_for_ty`
- `fn add_value_members(`
- `fn member_lookup_ty`
- `fn add_nominal_member_items`
- `fn add_nominal_members(`
- `fn add_type_member_items`
- `fn add_type_members(`
- `fn add_symbol_member_item`
- `fn add_protocol_requirement_items`
- ...and 525 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (6s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (19s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `session_declarations_persist_across_evaluations`, `captured_print_output_returns_with_the_result`, `harness_sources_type_check`, `runner_handles_test_files_below_project_src`, `runner_reports_compile_errors_as_source_diagnostics`, `runner_counts_assertion_failures`, `runner_filter_runs_only_the_named_test`, `runner_json_reports_tests_and_preserves_user_output`, `functions_carry_their_finalized_effect_scheme`, `rejects_an_integer_literal_above_the_signed_64_bit_range`, `accepts_the_signed_64_bit_integer_boundaries`, `rejects_an_out_of_range_integer_pattern`, `assert_runs`, `run_renders_a_scalar_script_result_in_talk_syntax`, `run_executes_core_operators`, `run_executes_branches_recursion_and_loops`, `run_suppresses_a_unit_result`, `run_executes_an_explicit_entry_function`, `run_falls_back_to_main_when_there_is_no_script_body`, `run_builds_projects_and_destructures_tuples` and 32 more.
- Existing test surfaces changed: `src/typed_ast/typed_ast_tests.rs`, `src/types/types_tests.rs`, `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - reviewed TOOL-06 rendering); 907 workspace tests pass. Backend size:

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
