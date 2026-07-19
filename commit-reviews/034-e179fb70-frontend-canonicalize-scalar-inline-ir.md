# Commit 034: `e179fb70` - frontend: canonicalize scalar inline IR

| Field | Value |
|---|---|
| Commit | `e179fb705fad13b6b4faec42dc6042f285d71be4` |
| Parent reviewed | `536e3efbdef3593c465bc6d93e730922a756fc50` |
| Author date | 2026-07-14T23:27:40-07:00 |
| Author | Pat Nakajima |
| Patch size | 15 files, +905 / -120 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 15.
- Production Rust: 9 files (+806/-78): `src/compiling/typed_program.rs`, `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/types/generate/artifacts.rs`, `src/types/generate/expr.rs`, `src/types/generate/finalize.rs`, `src/types/generate/func.rs`, `src/types/generate/mod.rs`, and 1 more.
- Documentation and plans: 6 files (+99/-42): `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md`, `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/e1-scalar-execution-plan.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/typed_program/contract.rs` | 461 | 39 |
| `src/types/generate/expr.rs` | 213 | 17 |
| `src/compiling/typed_program/build.rs` | 88 | 6 |
| `docs/e1-scalar-execution-plan.md` | 19 | 24 |
| `docs/stage-0-contract-types.md` | 38 | 0 |
| `docs/adr/0032-single-artifact-ownership-and-lowering-pipeline.md` | 20 | 5 |
| `src/compiling/typed_program.rs` | 10 | 9 |
| `docs/backend-status.md` | 13 | 4 |
| `src/types/generate/mod.rs` | 12 | 2 |
| `src/types/output.rs` | 9 | 2 |
| `docs/backend-parity-plan.md` | 5 | 5 |
| `src/types/generate/func.rs` | 5 | 3 |
| `docs/backend-parity-ledger.md` | 4 | 4 |
| `src/types/generate/artifacts.rs` | 6 | 0 |
| `src/types/generate/finalize.rs` | 2 | 0 |

### Representative declarations touched

- `pub struct Expr {`
- `struct InlineIr`
- `enum CheckedInlineIrOperation`
- `enum ScalarIntrinsicOperand`
- `pub struct HandlerFacts {`
- `struct CanonicalBuilder<'a> {`
- `impl<'a> CanonicalBuilder<'a> {`
- `fn checked_inline_ir_operation`
- `fn scalar_intrinsic_operand`
- `impl fmt::Display for TypedProgram {`
- `pub enum ExprKind {`
- `pub struct InlineIr {`
- `fn fmt`
- `fn scalar_type`
- `fn type_from_ty`
- `pub enum TypedProgramInvariant {`
- `impl TypedProgramValidator<'_> {`
- `fn validate_block`
- ...and 15 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (5s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (23s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `type_checker_publishes_canonical_scalar_intrinsics`, `core_operator_intrinsics_are_all_canonical`, `validator_rejects_noncanonical_scalar_intrinsic_operands`, `validator_rejects_scalar_parameter_from_another_callable`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
