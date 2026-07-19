# Commit 038: `9ba7c06a` - frontend: validate signed integer literals

| Field | Value |
|---|---|
| Commit | `9ba7c06abcfcfc594630536b42e9af2319b12ba1` |
| Parent reviewed | `3f36db1fa057ba772bdc244f853071fca3160a28` |
| Author date | 2026-07-15T00:54:14-07:00 |
| Author | Pat Nakajima |
| Patch size | 24 files, +379 / -67 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 24.
- Production Rust: 17 files (+302/-35): `src/compiling/contracts.rs`, `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/desugar/lower_operators.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/parsing/parser.rs`, `src/parsing/parser_error.rs`, and 9 more.
- Tests and test oracles: 1 files (+10/-0): `src/parsing/parser_tests.rs`.
- Documentation and plans: 6 files (+67/-32): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 124 | 3 |
| `src/talk_ir/lowering.rs` | 38 | 4 |
| `src/mir/generate.rs` | 21 | 8 |
| `docs/stage-0-contract-types.md` | 24 | 5 |
| `docs/e1-scalar-execution-plan.md` | 12 | 12 |
| `src/compiling/typed_program/build.rs` | 18 | 4 |
| `src/types/generate/artifacts.rs` | 20 | 0 |
| `src/desugar/lower_operators.rs` | 20 | 0 |
| `docs/backend-status.md` | 13 | 4 |
| `src/mir/mod.rs` | 9 | 5 |
| `docs/backend-parity-ledger.md` | 6 | 7 |
| `src/talk_ir/mod.rs` | 6 | 6 |
| `src/parsing/parser_tests.rs` | 10 | 0 |
| `src/parsing/parser.rs` | 9 | 1 |
| `src/types/output.rs` | 9 | 0 |

### Representative declarations touched

- `pub struct Expr {`
- `enum Literal`
- `pub enum PatternKind {`
- `pub enum Constant {`
- `pub enum IrConstant {`
- `pub struct ValueCoercions {`
- `impl TypedTreeBuilder<'_> {`
- `impl<'a> CanonicalBuilder<'a> {`
- `pub enum TypedProgramInvariant {`
- `impl TypedProgramValidator<'_> {`
- `fn validate_literal`
- `fn integer_literal_boundaries_are_canonical_signed_values`
- `fn out_of_range_integer_literals_diagnose_and_cannot_validate`
- `impl LowerOperators {`
- `fn folds_negative_integer_literals_before_operator_lowering`
- `impl<'program> FunctionGenerator<'program> {`
- `fn lower_literal`
- `impl<'a> Parser<'a> {`
- ...and 16 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (5s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (21s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `integer_literal_boundaries_are_canonical_signed_values`, `out_of_range_integer_literals_diagnose_and_cannot_validate`, `folds_negative_integer_literals_before_operator_lowering`, `rejects_out_of_range_inline_ir_integer_without_panicking`.
- Existing test surfaces changed: `src/parsing/parser_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
