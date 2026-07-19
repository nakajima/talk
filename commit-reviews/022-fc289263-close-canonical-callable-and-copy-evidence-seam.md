# Commit 022: `fc289263` - close canonical callable and Copy evidence seam

| Field | Value |
|---|---|
| Commit | `fc2892638a2d6108fdb5cac4f8a67aba1f69c026` |
| Parent reviewed | `a1a0ba902a19bc799fd7d6674097c2356801271b` |
| Author date | 2026-07-14T12:04:23-07:00 |
| Author | Pat Nakajima |
| Patch size | 33 files, +1199 / -707 |
| Review result | **Standalone defect, repaired later** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 33.
- Production Rust: 31 files (+1054/-451): `src/analysis/completion.rs`, `src/analysis/hover.rs`, `src/analysis/rename.rs`, `src/analysis/workspace.rs`, `src/compiling/module.rs`, `src/compiling/typed_program.rs`, `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, and 23 more.
- Tests and test oracles: 2 files (+145/-256): `src/typed_ast/typed_ast_tests.rs`, `src/types/types_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 366 | 21 |
| `src/typed_ast/typed_ast_tests.rs` | 106 | 238 |
| `src/compiling/typed_program/build.rs` | 140 | 84 |
| `src/analysis/completion.rs` | 55 | 145 |
| `src/types/generate/finalize.rs` | 153 | 0 |
| `src/analysis/hover.rs` | 68 | 31 |
| `src/lsp/code_actions.rs` | 32 | 52 |
| `src/types/ty.rs` | 54 | 23 |
| `src/types/types_tests.rs` | 39 | 18 |
| `src/compiling/module.rs` | 48 | 0 |
| `src/name_resolution/symbol.rs` | 2 | 34 |
| `src/mir/generate.rs` | 19 | 10 |
| `src/types/generate/func.rs` | 24 | 3 |
| `src/types/solve/var_store.rs` | 22 | 2 |
| `src/types/generate/collect.rs` | 10 | 10 |

### Representative declarations touched

- `pub struct CompletionAnalysis<'a> {`
- `pub fn complete_in_workspace(`
- `pub fn complete(`
- `fn scope_completions(analysis: &CompletionAnalysis<'_>, byte_offset: u32) -> Vec`
- `fn member_completions(analysis: &CompletionAnalysis<'_>, dot_offset: u32) -> Vec`
- `fn member_completion_receiver(ast: &AST<NameResolved>, dot_offset: u32) -> Optio`
- `fn add_value_members(`
- `fn add_nominal_members(`
- `fn add_callable_item(`
- `fn conformance_requirement_completions(`
- `fn type_annotation_symbol(annotation: &TypeAnnotation) -> Option<Symbol> {`
- `pub fn hover_at(`
- `pub fn hover_for_node_id(`
- `fn hover_for_node(workspace: &Workspace, node: &Node) -> Option<Hover> {`
- `fn hover_for_typed_pattern(`
- `fn hover_for_symbol`
- `fn hover_for_name(`
- `fn symbol_for_associated_type_member(`
- ...and 94 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` **failed** at this exact commit (6s). See Findings.
- Historical checkout: `cargo test --locked --quiet` **failed during compilation** at this exact commit (6s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `producer_records_scalar_copy_evidence`, `producer_records_generic_copy_predicate_evidence`, `producer_records_custom_copy_conformance_evidence`, `producer_records_conditional_copy_conformance_evidence`, `producer_records_phantom_copy_evidence`, `imported_bodyless_direct_call_has_stable_external_linkage`.
- Existing test surfaces changed: `src/typed_ast/typed_ast_tests.rs`, `src/types/types_tests.rs`.

## Findings

### 1. [P1] Finish updating MIR and contract fixtures before landing the seam change

- Location: `src/mir/generate.rs` and `src/compiling/typed_program/contract.rs`
- Status: **Fixed by the next commit, `1fb9946b`**
- Impact: The follow-up reduces the prior migration failures but remains non-buildable. The library still reads a removed `FunctionGenerator.program` field, while all-target test compilation also has one `TypedStruct` initializer without `effect_parameters` and two `CallFacts` initializers without `callee_origin`/`callee_value`.
- Evidence: `cargo check --all-targets --locked` fails at this exact commit with 4 Rust errors.
- Recommended correction: Include the four fixture/consumer updates that landed in `1fb9946b` so this commit is independently green.

## Disposition

Do not use this as an independently mergeable/bisectable commit. The cited later commit repairs the defect, but the history should ideally be squashed or reordered so every retained commit is green.
