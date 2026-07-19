# Commit 021: `a1a0ba90` - implement canonical TypedProgram types lane

| Field | Value |
|---|---|
| Commit | `a1a0ba902a19bc799fd7d6674097c2356801271b` |
| Parent reviewed | `14691b5491fc6768417c1a091ce1738274c07f1f` |
| Author date | 2026-07-14T10:47:23-07:00 |
| Author | Pat Nakajima |
| Patch size | 27 files, +5196 / -2973 |
| Review result | **Standalone defect, repaired later** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 27.
- Production Rust: 25 files (+5062/-2741): `src/analysis/completion.rs`, `src/analysis/definition.rs`, `src/analysis/hover.rs`, `src/analysis/rename.rs`, `src/analysis/workspace.rs`, `src/compiling/contracts.rs`, `src/compiling/core.rs`, `src/compiling/driver.rs`, and 17 more.
- Tests and test oracles: 1 files (+128/-227): `src/types/types_tests.rs`.
- Documentation and plans: 1 files (+6/-5): `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/build.rs` | 2391 | 16 |
| `src/compiling/typed_program/contract.rs` | 1501 | 54 |
| `src/lsp/rename.rs` | 16 | 931 |
| `src/analysis/completion.rs` | 332 | 501 |
| `src/lsp/goto_definition.rs` | 15 | 586 |
| `src/types/types_tests.rs` | 128 | 227 |
| `src/lsp/code_actions.rs` | 187 | 109 |
| `src/analysis/hover.rs` | 94 | 103 |
| `src/analysis/rename.rs` | 98 | 69 |
| `src/analysis/definition.rs` | 101 | 33 |
| `src/compiling/module.rs` | 97 | 30 |
| `src/compiling/driver.rs` | 35 | 62 |
| `src/compiling/contracts.rs` | 58 | 28 |
| `src/compiling/typed_program.rs` | 12 | 63 |
| `src/typed_ast/mod.rs` | 15 | 39 |

### Representative declarations touched

- `pub struct CompletionAnalysis<'a> {`
- `pub fn complete_in_workspace(`
- `pub fn complete(`
- `fn member_completion_dot(text: &str, byte_offset: u32) -> Option<u32> {`
- `fn is_ident_byte(b: u8) -> bool {`
- `fn member_completions(analysis: &CompletionAnalysis<'_>, dot_offset: u32) -> Vec`
- `fn member_completion_receiver(ast: &AST<NameResolved>, dot_offset: u32) -> Optio`
- `fn type_receiver_symbol(receiver: &Expr) -> Option<Symbol> {`
- `fn member_lookup_ty`
- `fn add_value_members`
- `fn add_member_items_for_ty(`
- `fn add_nominal_members`
- `fn add_nominal_member_items(`
- `fn add_type_members`
- `fn add_type_member_items(`
- `fn add_protocol_members`
- `fn add_callable_item`
- `fn add_item`
- ...and 222 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` **failed** at this exact commit (6s). See Findings.
- Historical checkout: `cargo test --locked --quiet` **failed during compilation** at this exact commit (6s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `type_checker_publishes_a_valid_copy_program`, `core_frontend_artifact_validates`.
- Existing test surfaces changed: `src/types/types_tests.rs`.

## Findings

### 1. [P1] Keep the TypedProgram migration buildable as an atomic commit

- Location: `src/compiling/typed_program/build.rs`, `contract.rs`, and their consumers
- Status: **Fixed later by `1fb9946b`**
- Impact: The contract types are changed before all producers, consumers, and tests are migrated. An exact checkout reports 46 compiler errors: stale `TypedFunction.body` accesses after the field became `implementation`, unconstructed `UseMode::Copy`/`CaptureMode::Copy` tuple variants, missing `CallFacts.callee_origin`, a missing `TypedStruct.effect_parameters`, and a non-exhaustive `ExprKind::Error` match. This commit cannot be built or used as a bisect point.
- Evidence: `cargo check --all-targets --locked` fails at this exact commit with 46 Rust errors.
- Recommended correction: Fold the producer/consumer migration from the follow-up fixes into this commit, or split the schema changes behind a compiling compatibility step.

## Disposition

Do not use this as an independently mergeable/bisectable commit. The cited later commit repairs the defect, but the history should ideally be squashed or reordered so every retained commit is green.
