# Commit 128: `d31a88a9` - Design wave 9: drop emission rework

| Field | Value |
|---|---|
| Commit | `d31a88a970cb23e0b608fc82d6387fdd8353aa17` |
| Parent reviewed | `155fbf8d0b0e19a60903c2d0c0973ebd6c18fd8f` |
| Author date | 2026-07-17T17:05:45-07:00 |
| Author | Pat Nakajima |
| Patch size | 1 files, +95 / -0 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Records the post-profiling design for the three drop-emission fixes:
memoized deinit/needs_drop queries, routing ordinary drop sites
through the existing per-type Glue::Drop functions, and per-function
cleanup chains in place of per-call-site cleanup synthesis. The
chain design rests on the invariant merge_arms already enforces —
the owned live set is path-independent at every join — so no runtime
drop flags are needed. Measured motivation and exit criteria are in
the section; targets: backend compile ~400ms -> ~250ms, emitted MIR
~143k -> ~120k instructions.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 1.
- Documentation and plans: 1 files (+95/-0): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `docs/lean-backend-rebuild-plan.md` | 95 | 0 |

### Representative declarations touched

- `enum type`

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
