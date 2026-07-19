# Commit 050: `4ec07011` - l1: specialize local scalar calls

| Field | Value |
|---|---|
| Commit | `4ec070111fc3b3baac44cf8791f133f68a473d47` |
| Parent reviewed | `fe6b86861a18a722902d147a3a8e1ba02677d806` |
| Author date | 2026-07-15T12:52:50-07:00 |
| Author | Pat Nakajima |
| Patch size | 9 files, +1334 / -208 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: M: 9.
- Production Rust: 6 files (+1260/-191): `src/compiling/typed_program/build.rs`, `src/compiling/typed_program/contract.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/verify.rs`, `src/talk_ir/lowering.rs`.
- Tests and test oracles: 1 files (+24/-1): `tests/talk_tests.rs`.
- Documentation and plans: 2 files (+50/-16): `docs/backend-parity-ledger.md`, `docs/backend-status.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/talk_ir/lowering.rs` | 589 | 123 |
| `src/mir/verify.rs` | 224 | 42 |
| `src/mir/generate.rs` | 208 | 18 |
| `src/mir/mod.rs` | 121 | 1 |
| `src/compiling/typed_program/build.rs` | 57 | 7 |
| `src/compiling/typed_program/contract.rs` | 61 | 0 |
| `docs/backend-status.md` | 45 | 11 |
| `tests/talk_tests.rs` | 24 | 1 |
| `docs/backend-parity-ledger.md` | 5 | 5 |

### Representative declarations touched

- `impl<'a> CanonicalBuilder<'a> {`
- `fn canonical_call_instantiation`
- `fn producer_publishes_complete_ordered_recursive_generic_instantiations`
- `impl<'program> FunctionGenerator<'program> {`
- `fn preserves_complete_generic_and_recursive_call_instantiations`
- `fn rejects_protocol_defaults_without_a_frontend_selected_implementation`
- `pub enum Callee {`
- `fn source_candidate`
- `fn generic_call_candidate`
- `fn generic_call`
- `fn verifies_generic_call_arity_and_concreteness`
- `fn rejects_a_mismatched_selected_implementation`
- `impl<'mir> MirVerifier<'mir> {`
- `fn specialized_call_contract`
- `fn verify_contract_storage_ty`
- `fn storage_class_for_contract`
- `pub(crate) fn lower(mir: &CheckedMir) -> Result<TalkIrModule, LoweringError> {`
- `struct SpecializationKey`
- ...and 24 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (6s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (23s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `producer_publishes_complete_ordered_recursive_generic_instantiations`, `preserves_complete_generic_and_recursive_call_instantiations`, `rejects_protocol_defaults_without_a_frontend_selected_implementation`, `verifies_generic_call_arity_and_concreteness`, `rejects_a_mismatched_selected_implementation`, `specializes_generic_scalar_calls_once_per_canonical_key`, `preallocates_recursive_generic_specializations_and_executes_them`, `materializes_exact_frontend_selected_local_implementations`, `rejects_external_selected_implementation_specialization_supply`, `run_executes_local_generic_scalar_specializations`.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
