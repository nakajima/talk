# Commit 135: `1d20c13b` - 11a: bind names to their rvalue temporaries without a copy

| Field | Value |
|---|---|
| Commit | `1d20c13b501ea05da5abf781ad6b312690c988b5` |
| Parent reviewed | `46ac30792aa07f2eecc39a15785fafb069298718` |
| Author date | 2026-07-17T19:48:35-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +79 / -5 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

A `let` (and every pattern bind reached through bind_owned_pattern —
tuple elements, match-arm payloads) allocated a fresh local and
copied the initializer into it. When the initializer is a frame-owned
statement temporary, the binding now takes the temporary's local as
its storage: a name for a value, not a copy of one — the straight-
line half of on-the-fly SSA construction (Braun, Buchwald, Hack,
Leissa, Mallon & Zwinkau, CC 2013). Parameters and other bindings
keep their own storage (aliasing a parameter would corrupt writeback;
aliasing another binding would fuse two lifetimes under one moved
flag). Ownership bookkeeping is unchanged by construction: the same
consume-then-own sequence runs against the same local id.

Shape test pins it: a let chain renders with zero copies and runs
leak-free. talk-syntax: 0.81s -> 0.79s. All gates green: 964
workspace, 18 core, 225 talk-syntax, 1 talk-html.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+19/-5): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+60/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `tests/talk_tests.rs` | 60 | 0 |
| `src/backend/mir.rs` | 19 | 5 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn assert_parity_program(name: &str) {`
- `fn owned_bindings_alias_their_rvalue_temporaries`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (34s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `owned_bindings_alias_their_rvalue_temporaries`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - leak-free. talk-syntax: 0.81s -> 0.79s. All gates green: 964

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
