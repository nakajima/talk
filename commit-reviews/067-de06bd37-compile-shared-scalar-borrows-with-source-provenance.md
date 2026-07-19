# Commit 067: `de06bd37` - Compile shared scalar borrows with source provenance

| Field | Value |
|---|---|
| Commit | `de06bd37226be6afb3ecb0a5079a2177750c0d24` |
| Parent reviewed | `73759ae6ef9401bd56b5dd78a7e903ed521e2fc5` |
| Author date | 2026-07-15T23:43:11-07:00 |
| Author | Pat Nakajima |
| Patch size | 13 files, +1946 / -79 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the staged contracts/Talk IR backend phase. Backend portions are largely superseded by the lean rebuild in `ee03e896` (commit 069); frontend, contract, runtime, and documentation changes may remain relevant.

## Patch analysis

- File operations: A: 1, M: 12.
- Production Rust: 8 files (+1866/-48): `src/lsp/borrow_provenance.rs`, `src/mir/generate.rs`, `src/mir/mod.rs`, `src/mir/provenance.rs`, `src/mir/provenance/context.rs`, `src/mir/provenance/production.rs`, `src/mir/verify.rs`, `src/talk_ir/lowering.rs`.
- Tests and test oracles: 1 files (+26/-0): `tests/talk_tests.rs`.
- Documentation and plans: 4 files (+54/-31): `docs/backend-parity-ledger.md`, `docs/backend-parity-plan.md`, `docs/backend-status.md`, `docs/stage-0-contract-types.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/mir/provenance/production.rs` | 695 | 0 |
| `src/mir/verify.rs` | 588 | 18 |
| `src/mir/generate.rs` | 379 | 18 |
| `src/lsp/borrow_provenance.rs` | 97 | 1 |
| `src/talk_ir/lowering.rs` | 46 | 11 |
| `src/mir/mod.rs` | 56 | 0 |
| `docs/backend-status.md` | 36 | 16 |
| `tests/talk_tests.rs` | 26 | 0 |
| `docs/backend-parity-plan.md` | 14 | 11 |
| `docs/backend-parity-ledger.md` | 3 | 3 |
| `src/mir/provenance/context.rs` | 4 | 0 |
| `docs/stage-0-contract-types.md` | 1 | 1 |
| `src/mir/provenance.rs` | 1 | 0 |

### Representative declarations touched

- `pub enum MirInvariant {`
- `pub(crate) fn render_borrow_provenance(`
- `fn render_borrow_provenance_at`
- `fn renders_source_backed_shared_borrow_provenance`
- `fn renders_source_backed_branch_specific_borrow_endings`
- `struct FunctionGenerator<'program> {`
- `impl<'program> FunctionGenerator<'program> {`
- `fn borrow_origin`
- `fn new_loan`
- `fn incoming_loan`
- `fn begin_shared_borrow`
- `fn begin_shared_borrowed_value`
- `fn end_temporary_borrow`
- `struct BorrowTemporary`
- `fn generates_shared_scalar_loans_transfers_uses_and_endings`
- `fn rejects_malformed_shared_borrow_lifetimes_and_transfers`
- `impl BorrowEventKind {`
- `impl<'mir> BorrowProvenanceContext<'mir> {`
- ...and 34 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (5s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (25s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `renders_source_backed_shared_borrow_provenance`, `renders_source_backed_branch_specific_borrow_endings`, `generates_shared_scalar_loans_transfers_uses_and_endings`, `rejects_malformed_shared_borrow_lifetimes_and_transfers`, `erases_verified_shared_scalar_loans_after_mir`, `run_executes_a_shared_borrowed_scalar_parameter`.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
