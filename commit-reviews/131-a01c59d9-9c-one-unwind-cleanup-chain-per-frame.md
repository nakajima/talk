# Commit 131: `a01c59d9` - 9c: one unwind cleanup chain per frame

| Field | Value |
|---|---|
| Commit | `a01c59d9c3cfd48e972c2a7271551e04a3abf5d5` |
| Parent reviewed | `8350e3b7e90245c3d42a6ac29564e6e1c020bbf4` |
| Author date | 2026-07-17T18:03:49-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +134 / -19 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Every suspendable call synthesized its own cleanup block — cloning
three tracking maps and re-dropping the whole live set from scope 0 —
measured at 2,714 blocks and 19,060 instructions (13.3% of emitted
MIR) on the talk-syntax corpus, for abort paths that almost never
run. Cleanup is now a chain: each node drops one live value (through
9b's shared drop functions) and jumps toward the outermost node,
which ends in UnwindRet; a call site's unwind target is the chain's
innermost node for its current live set. The chain self-heals by
longest-common-prefix comparison against the live list, so a
mid-stack consume invalidates only the nodes above it, and no
snapshot/restore of builder state is needed at all. Static drop-flag-
free chains are sound because merge_arms reconciles moves at every
join: the owned live set is path-independent (the shape of shared
landing pads in zero-cost exception handling — de Dinechin, IEEE
Concurrency 2000).

New test pins the shape: three calls over an unchanged live set
produce exactly one UnwindRet block, and the program runs leak-free.
All gates green: 962 workspace (effects cluster's abort pins
included), 18 core, 225 talk-syntax, 1 talk-html.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+67/-19): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+67/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 67 | 19 |
| `tests/talk_tests.rs` | 67 | 0 |

### Representative declarations touched

- `struct ProgramBuilder<'a> {`
- `struct CleanupNode`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn assert_parity_program(name: &str) {`
- `fn unwind_cleanup_is_one_chain_per_function`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (38s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `unwind_cleanup_is_one_chain_per_function`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - All gates green: 962 workspace (effects cluster's abort pins

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
