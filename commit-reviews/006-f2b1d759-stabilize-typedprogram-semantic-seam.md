# Commit 006: `f2b1d759` - stabilize TypedProgram semantic seam

| Field | Value |
|---|---|
| Commit | `f2b1d7592335551b32779b27890ec4654caccec4` |
| Parent reviewed | `a1d20d27fd25db78005c90759993bfb85641424e` |
| Author date | 2026-07-13T17:55:20-07:00 |
| Author | Pat Nakajima |
| Patch size | 8 files, +180 / -135 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 8.
- Production Rust: 7 files (+108/-116): `src/compiling/typed_program/build.rs`, `src/typed_ast/mod.rs`, `src/types/catalog.rs`, `src/types/generate/finalize.rs`, `src/types/output.rs`, `src/types/solve/mod.rs`, `src/types/solve/unify.rs`.
- Tests and test oracles: 1 files (+72/-19): `src/typed_ast/typed_ast_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/build.rs` | 59 | 42 |
| `src/typed_ast/typed_ast_tests.rs` | 72 | 19 |
| `src/typed_ast/mod.rs` | 30 | 42 |
| `src/types/catalog.rs` | 6 | 13 |
| `src/types/generate/finalize.rs` | 5 | 7 |
| `src/types/output.rs` | 4 | 6 |
| `src/types/solve/unify.rs` | 2 | 4 |
| `src/types/solve/mod.rs` | 2 | 2 |

### Representative declarations touched

- `impl TypedTreeBuilder<'_> {`
- `fn node`
- `fn binding_ty`
- `pub enum Node {`
- `struct ValueCoercions`
- `pub struct Expr {`
- `impl std::fmt::Debug for Expr {`
- `pub enum Literal {`
- `pub enum ExprKind {`
- `pub struct Pattern {`
- `pub struct RecordFieldPattern {`
- `pub enum DeclKind {`
- `fn build_typed_files`
- `fn lower(source: &str) -> Vec<(Vec<Node>, Vec<typed_ast::Node>)> {`
- `fn typed_expr_ids`
- `fn collect_expr(e: &typed_ast::Expr, ids: &mut Vec<NodeID>) {`
- `fn collect_stmt(s: &typed_ast::Stmt, ids: &mut Vec<NodeID>) {`
- `fn lowers_a_construct_diverse_program_without_panicking() {`
- ...and 10 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (3s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (9s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `value_coercions_are_baked_in_execution_order`, `pattern_bindings_carry_their_checked_types`.
- Existing test surfaces changed: `src/typed_ast/typed_ast_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
