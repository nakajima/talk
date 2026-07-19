# Commit 134: `46ac3079` - Record wave 10 closure and design wave 11: SSA-form MIR

| Field | Value |
|---|---|
| Commit | `46ac30792aa07f2eecc39a15785fafb069298718` |
| Parent reviewed | `43c6c050a1770efa0ee150afb08de6e1208dc080` |
| Author date | 2026-07-17T19:33:28-07:00 |
| Author | Pat Nakajima |
| Patch size | 1 files, +134 / -0 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Wave 11's motivation is measured, not assumed: after wave 10, Const
is the most-executed opcode at 4.35M of ~21M instructions (~22%) —
loops re-materialize constants every iteration, which no block-local
cache can fix — while Moves already fell to 3.1% under coalescing
hints. The design: block-parameter SSA (Appel 1998) built with the
Braun et al. CC 2013 algorithm (single pass, no dominance
computation — fits the existing builder), ownership tracking keyed
on values (moved becomes monotone; the wave-9 join invariant becomes
"a parameter is owned on every edge or none"), and the linear scan
extended per Wimmer & Franz CGO 2010 with Boissinot et al. CGO 2009
edge-move resolution. Three phases, each gated: copy folding in the
builder, block parameters, SSA allocation.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 1.
- Documentation and plans: 1 files (+134/-0): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `docs/lean-backend-rebuild-plan.md` | 134 | 0 |

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
