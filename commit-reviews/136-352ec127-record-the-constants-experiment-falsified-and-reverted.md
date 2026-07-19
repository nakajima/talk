# Commit 136: `352ec127` - Record the constants experiment: falsified and reverted

| Field | Value |
|---|---|
| Commit | `352ec1275063ccf630b878c12de8680c007fa0f3` |
| Parent reviewed | `1d20c13b501ea05da5abf781ad6b312690c988b5` |
| Author date | 2026-07-17T20:04:41-07:00 |
| Author | Pat Nakajima |
| Patch size | 1 files, +39 / -0 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

A loop-invariant constant-placement pass (entry-block definitions
for constants used in layout-order loop intervals) was built and
measured: executed Const barely moved (4.35M -> 4.18M) while
executed Move tripled (0.66M -> 1.6M). The opcode histogram shows
the 4.35M constant loads are per-call materializations in hot leaf
functions — the loop is in the caller, so no intra-function
placement can amortize them. The pass is reverted; the finding and
the real options (Lua-style register-or-constant operands, deeper
inlining, or accepting the load) are recorded in the plan for a
deliberate decision. Also recorded: this machine throttled 4.34GHz
-> 3.79GHz across the session's benchmarking tail, so instruction
counts, not wall clock, were the reliable signal.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 1.
- Documentation and plans: 1 files (+39/-0): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `docs/lean-backend-rebuild-plan.md` | 39 | 0 |

## Test and validation review

- Historical checkout compilation was not repeated because this patch changes only documentation/language fixtures/oracles and no Rust or Cargo inputs.
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (34s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
