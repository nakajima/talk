# Commit 123: `6cb99c99` - Close wave 3: enforce the final flow-corpus batch

| Field | Value |
|---|---|
| Commit | `6cb99c995905ba946d690678ca1e1a502dfb9a39` |
| Parent reviewed | `bbacd632ac8c56d7ad65ef902fc2da9a0a7eda5d` |
| Author date | 2026-07-17T13:26:31-07:00 |
| Author | Pat Nakajima |
| Patch size | 7 files, +110 / -34 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Four rules land: taking an owned non-Copy/CheapClone value out of a
shared borrow rejects (donation-path check, rooted in borrow
provenance; rigid parameter bounds satisfy via conforms_to, which now
reads catalog param_bounds); calling a `mut func` through a shared
borrow rejects; cloning a linear value rejects; match-join results
carry arm-value provenance so borrows returned through expression
matches keep their roots. Dropping an owned (consume-marked)
parameter is now a sanctioned linear disposal, matching consuming
receivers — the callee owns the disposal (this is what let the copy
marker reject surface instead of the callee's own drop). Borrow
params record local_tys entries during instance compile, which the
new checks read. Core-module frames are exempt from the extraction
rule (manual buffer discipline, same as return donation).

The flow gate enforces 170 of 183; the 13-name tail is argued or
refinement work, recorded in the plan's wave-3 closure note. All
other gates stay green: 950 workspace, 18 core, 225 talk-syntax,
1 talk-html.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 7.
- Production Rust: 1 files (+68/-0): `src/backend/mir.rs`.
- Tests and test oracles: 5 files (+4/-11): `tests/reference/flow/expected/borrow_of_one_argument_still_rejects_moving_that_argument.error`, `tests/reference/flow/expected/record_containing_borrow_tracks_owner_invalidation.error`, `tests/reference/flow/expected/rejects_binding_non_cheap_clone_field_from_shared_borrow.error`, `tests/reference/flow/expected/rejects_returning_non_cheap_clone_field_from_shared_borrow.error`, `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+38/-23): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 68 | 0 |
| `docs/lean-backend-rebuild-plan.md` | 38 | 23 |
| `tests/talk_tests.rs` | 0 | 7 |
| `tests/reference/flow/expected/rejects_returning_non_cheap_clone_field_from_shared_borrow.error` | 1 | 1 |
| `tests/reference/flow/expected/rejects_binding_non_cheap_clone_field_from_shared_borrow.error` | 1 | 1 |
| `tests/reference/flow/expected/record_containing_borrow_tracks_owner_invalidation.error` | 1 | 1 |
| `tests/reference/flow/expected/borrow_of_one_argument_still_rejects_moving_that_argument.error` | 1 | 1 |

### Representative declarations touched

- `fn conforms_to(builder: &ProgramBuilder<'_>, head: Symbol, protocol: Symbol) ->`
- `impl<'a> ProgramBuilder<'a> {`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (39s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/reference/flow/expected/borrow_of_one_argument_still_rejects_moving_that_argument.error`, `tests/reference/flow/expected/record_containing_borrow_tracks_owner_invalidation.error`, `tests/reference/flow/expected/rejects_binding_non_cheap_clone_field_from_shared_borrow.error`, `tests/reference/flow/expected/rejects_returning_non_cheap_clone_field_from_shared_borrow.error`, `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - other gates stay green: 950 workspace, 18 core, 225 talk-syntax,

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
