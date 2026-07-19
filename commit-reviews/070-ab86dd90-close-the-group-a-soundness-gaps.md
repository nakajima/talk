# Commit 070: `ab86dd90` - Close the group-A soundness gaps

| Field | Value |
|---|---|
| Commit | `ab86dd902efc2bac9e2057147221334c57512953` |
| Parent reviewed | `ee03e8960def53c690e586e589e96933d265588d` |
| Author date | 2026-07-16T09:05:30-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +189 / -24 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Three correctness holes recorded at parity, each driven by a failing
black-box test:

- Reject owned-value captures in function values and trailing blocks
  (CHG-06: v1 captures are Copy values and handler-extent shared
  borrows); a closure environment copy could outlive its owner.
- Run guarded global teardown on every exit: the script entry now splits
  into an outer frame (teardown, result delivery) and an inner frame
  (statements and handler installs), so a handler clause's structural
  Discontinue no longer skips teardown.
- Reject owned payloads performed through generic effects: one clause
  body serves every instantiation over rigid payload types and cannot
  drop an owned payload.

910 workspace tests pass; backend at 4,546 production lines
(<=10,716 of the 13,400 budget).

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 1 files (+120/-24): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+45/-0): `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+24/-0): `docs/lean-rebuild-wave-reports.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 120 | 24 |
| `tests/talk_tests.rs` | 45 | 0 |
| `docs/lean-rebuild-wave-reports.md` | 24 | 0 |

### Representative declarations touched

- `fn ty_has_projection(ty: &Ty) -> bool {`
- `fn ty_has_any_param`
- `struct Search`
- `fn fold_param`
- `impl<'a> ProgramBuilder<'a> {`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn check_captures`
- `fn parity_effectful_closures() {`
- `fn run_rejects_owned_captures_in_closures`
- `fn run_tears_down_globals_after_a_top_level_discontinue`
- `fn run_rejects_owned_payloads_through_generic_effects`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (10s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `run_rejects_owned_captures_in_closures`, `run_tears_down_globals_after_a_top_level_discontinue`, `run_rejects_owned_payloads_through_generic_effects`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 910 workspace tests pass; backend at 4,546 production lines

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
