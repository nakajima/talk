# Commit 023: `1fb9946b` - fix typed program review blockers

| Field | Value |
|---|---|
| Commit | `1fb9946bf65df5740d23f7cbfa38662b432e1627` |
| Parent reviewed | `fc2892638a2d6108fdb5cac4f8a67aba1f69c026` |
| Author date | 2026-07-14T14:58:18-07:00 |
| Author | Pat Nakajima |
| Patch size | 15 files, +939 / -1513 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 15.
- Production Rust: 13 files (+886/-1498): `src/analysis/definition.rs`, `src/analysis/rename.rs`, `src/compiling/contracts.rs`, `src/compiling/module.rs`, `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/parsing/node_kinds/func.rs`, and 5 more.
- Documentation and plans: 2 files (+53/-15): `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/analysis/rename.rs` | 46 | 937 |
| `src/analysis/definition.rs` | 25 | 509 |
| `src/compiling/typed_program/build.rs` | 422 | 6 |
| `src/compiling/typed_program/contract.rs` | 315 | 19 |
| `docs/backend-status.md` | 31 | 13 |
| `src/types/generate/finalize.rs` | 29 | 2 |
| `src/compiling/module.rs` | 5 | 22 |
| `docs/stage-0-contract-types.md` | 22 | 2 |
| `src/types/generate/func.rs` | 14 | 0 |
| `src/types/generate/expr.rs` | 13 | 0 |
| `src/parsing/parser.rs` | 5 | 2 |
| `src/mir/generate.rs` | 4 | 1 |
| `src/compiling/contracts.rs` | 4 | 0 |
| `src/types/generate/artifacts.rs` | 2 | 0 |
| `src/parsing/node_kinds/func.rs` | 2 | 0 |

### Representative declarations touched

- `pub enum UseMode {`
- `pub enum CaptureMode {`
- `pub struct TypedProgram {`
- `struct SemanticOccurrence`
- `pub fn goto_definition(`
- `fn goto_definition_from_import(`
- `fn module_start_location(module: &Workspace) -> Option<Location> {`
- `fn document_id_for_path(module: &Workspace, path: &Path) -> Option<DocumentId> {`
- `fn normalize_path(path: &Path) -> PathBuf {`
- `pub(crate) fn definition_location_for_symbol(`
- `pub struct TextEdit {`
- `fn rename_at`
- `fn is_valid_identifier(name: &str) -> bool {`
- `fn is_symbol_renamable(module: &Workspace, symbol: Symbol) -> bool {`
- `impl Module {`
- `impl TypedTreeBuilder<'_> {`
- `pub(crate) fn build_program(`
- `struct SourceOccurrenceCollector`
- ...and 40 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (6s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (17s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `producer_preserves_unproved_explicit_copy_as_invalid_copy`, `producer_preserves_unproved_copy_captures`, `module_interface_assigns_unique_links_to_generated_initializers`, `imported_intrinsics_remain_intrinsic`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
