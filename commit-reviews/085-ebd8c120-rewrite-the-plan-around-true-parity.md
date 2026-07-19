# Commit 085: `ebd8c120` - Rewrite the plan around true parity

| Field | Value |
|---|---|
| Commit | `ebd8c12042e588c359d15cf030a3e16c10779a8a` |
| Parent reviewed | `31cf410e807608ae3d27c5f628cc58c211c184a0` |
| Author date | 2026-07-16T23:02:11-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +100 / -1 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

System audit against every external Talk corpus on this machine, and a
governing plan revision that replaces proxy-parity with counted gates:

- Gates: G1 repo core suites (CI, green — 18 tests), G2 frozen corpus
  (CI, green — 16 programs), G3 external project suites (opt-in CI via
  TALK_ACCEPTANCE_DIRS; talk-syntax 207/223, talk-html green), G4
  embedding surfaces (green).
- Burn-down: the 16 open talk-syntax failures classified into five
  root-cause families with their trap signatures.
- Admitted coverage gaps: user effects outside the harness, remote
  package dependencies, wasm runtime, derived conformances beyond what
  talk-syntax reaches.
- Rules: parity vocabulary only as gate counts; ownership/generics/
  dispatch changes sweep G3 before merge; mine the archived
  implementations for encoded semantics before re-deriving; every
  rejection carries a message, a pinned test, and a justification.
- Audit notes: talispk and talk-test are blocked by frontend/stdlib
  drift (missing `reduce`; package.tlk-as-source manifest collision),
  not the backend.

Adds talk_test_runs_acceptance_projects (the G3 gate). 934 workspace
tests pass.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Tests and test oracles: 1 files (+26/-0): `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+74/-1): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `docs/lean-backend-rebuild-plan.md` | 74 | 1 |
| `tests/talk_tests.rs` | 26 | 0 |

### Representative declarations touched

- `fn talk_test_runs_the_core_suites() {`
- `fn talk_test_runs_acceptance_projects`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (1s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (9s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `talk_test_runs_acceptance_projects`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - - Gates: G1 repo core suites (CI, green — 18 tests), G2 frozen corpus
  - tests pass.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
