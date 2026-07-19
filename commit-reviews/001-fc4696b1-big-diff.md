# Commit 001: `fc4696b1` - big diff

| Field | Value |
|---|---|
| Commit | `fc4696b1631c9b29f0f95006f797f39b4fad9780` |
| Parent reviewed | `739f83dd3f1136729122d7122a4dfdaa46a435b5` |
| Author date | 2026-07-12T22:40:18-07:00 |
| Author | Pat Nakajima |
| Patch size | 87 files, +11645 / -1076 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the pre-reset implementation and is superseded by `a1d20d27` (commit 005 in this review set). It is still reviewed as an atomic historical patch.

## Patch analysis

- File operations: A: 8, M: 78, R: 1.
- Production Rust: 61 files (+5671/-1018): `src/compiling/driver.rs`, `src/compiling/typed_program/build.rs`, `src/flow/cfg.rs`, `src/flow/drops.rs`, `src/flow/grades.rs`, `src/flow/liveness.rs`, `src/flow/loans.rs`, `src/flow/mir_annotate.rs`, and 53 more.
- Tests and test oracles: 8 files (+4204/-22): `src/flow/flow_borrow_tests.rs`, `src/flow/flow_tests.rs`, `src/fuzz_tests.rs`, `src/lambda_g/balance_tests.rs`, `src/lower/lower_tests.rs`, `src/parsing/parser_tests.rs`, `src/types/types_tests.rs`, `src/vm/vm_tests.rs`.
- Language sources and benchmark fixtures: 4 files (+44/-14): `core/Array.test.tlk`, `core/Array.tlk`, `core/Memory.tlk`, `stdlib/fs.tlk`.
- Documentation and plans: 14 files (+1726/-22): `docs/adr/0011-dynamic-extent-effect-handlers.md`, `docs/adr/0017-structural-temp-drops-and-free-balance-verifier.md`, `docs/adr/0018-borrow-by-default-parameters.md`, `docs/adr/0021-first-class-iteration-and-borrow-default-for-loops.md`, `docs/adr/0027-effect-abort-unwinding.md`, `docs/adr/{0025-structured-diagnostics-and-conservative-code-actions.md => 0028-structured-diagnostics-and-conservative-code-actions.md}`, `docs/adr/0029-uniform-rc-baseline.md`, `docs/adr/0030-structural-drop-candidate-claiming.md`, and 6 more.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/fuzz_tests.rs` | 1536 | 0 |
| `src/lambda_g/balance.rs` | 1354 | 0 |
| `src/vm/vm_tests.rs` | 842 | 1 |
| `src/lower/mir.rs` | 547 | 115 |
| `src/lower/mir_lowering.rs` | 421 | 142 |
| `docs/adr/0027-effect-abort-unwinding.md` | 530 | 0 |
| `src/types/types_tests.rs` | 462 | 18 |
| `src/flow/moves.rs` | 370 | 102 |
| `src/lower/lower_tests.rs` | 437 | 3 |
| `docs/adr/0029-uniform-rc-baseline.md` | 426 | 0 |
| `src/flow/flow_tests.rs` | 412 | 0 |
| `talk-runtime/src/interp.rs` | 311 | 39 |
| `src/types/catalog.rs` | 280 | 23 |
| `src/lower/statements.rs` | 173 | 109 |
| `src/flow/cfg.rs` | 209 | 67 |

### Representative declarations touched

- `public struct Array<Element> {`
- `impl Driver<Typed> {`
- `impl Driver<Lowered> {`
- `fn assert_balance`
- `fn run_vm_fenced`
- `impl TypedTreeBuilder<'_> {`
- `pub(crate) fn check_bodies(`
- `enum Pass`
- `impl BodyWalk<'_, '_> {`
- `fn check_body(`
- `fn transfer_block(`
- `fn transfer_statement(`
- `fn classify_candidate(`
- `fn local_ty`
- `fn local_ty(`
- `struct HandlerBody`
- `fn handler_reentry_edges`
- `fn block_binders`
- ...and 492 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (9s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (35s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `inferred_param_caller_reuses_argument_after_call`, `inferred_consume_param_still_consumes`, `consume_marker_against_inferred_borrow_param_is_rejected`, `rejects_returning_non_cheap_clone_payload_binder_from_borrowed_scrutinee`, `rejects_storing_non_cheap_clone_payload_binder_into_owned_struct`, `rejects_tuple_nested_payload_binder_consume_from_borrowed_scrutinee`, `rejects_consume_argument_of_payload_binder_from_borrowed_scrutinee`, `rejects_consume_argument_of_cheap_clone_payload_binder_from_borrowed_scrutinee`, `clones_cheap_clone_payload_binder_returned_from_borrowed_scrutinee`, `generic_payload_binder_from_borrowed_self_rejects_non_cheap_instantiation`, `rejects_borrow_use_after_owner_reassignment_across_join`, `rejects_borrow_use_after_owner_reassignment_across_join_mirror`, `loan_owners_fold_over_every_owning_loan`, `rebased_perm_stays_exclusive_when_every_owner_is_exclusive`, `reports_top_level_flow_error_exactly_once`, `array_of_runtime_strings_result_passes_leak_fence`, `deinit_rebound_self_drops_without_redispatch`, `deinit_consuming_match_on_self_drops_without_redispatch`, `deinit_created_instance_still_dispatches_hook`, `heap_constructor_place_read_consume_params_balance` and 171 more.
- Existing test surfaces changed: `core/Array.test.tlk`, `src/flow/flow_borrow_tests.rs`, `src/flow/flow_tests.rs`, `src/fuzz_tests.rs`, `src/lambda_g/balance_tests.rs`, `src/lower/lower_tests.rs`, `src/parsing/parser_tests.rs`, `src/types/types_tests.rs`, `src/vm/vm_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
