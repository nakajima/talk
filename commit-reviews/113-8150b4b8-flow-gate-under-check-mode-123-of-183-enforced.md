# Commit 113: `8150b4b8` - Flow gate under check mode: 123 of 183 enforced

| Field | Value |
|---|---|
| Commit | `8150b4b8dd68687dc3a0b90524e1c78805c0271e` |
| Parent reviewed | `575c7f3b3a628d6f4221e07ee5b200aff12890f5` |
| Author date | 2026-07-17T10:24:50-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +26 / -8 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

The burn-down list regenerates from the definitive whole-program
sweep: 60 names, all in the deep provenance block (borrow
invalidation, escaping-borrow returns, borrow-typed positions, linear
path-sensitivity, loop-carried rules, unique parameters, marker
validation).

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Tests and test oracles: 1 files (+10/-8): `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+16/-0): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `tests/talk_tests.rs` | 10 | 8 |
| `docs/lean-backend-rebuild-plan.md` | 16 | 0 |

### Representative declarations touched

- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (1s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (27s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
