# Commit 142: `1566a24a` - Build memberwise constructions directly

| Field | Value |
|---|---|
| Commit | `1566a24a2a52bec8569e7fbd5de72127da393b41` |
| Parent reviewed | `d253119205049aaf648d838942d19e1dd89a5277` |
| Author date | 2026-07-17T22:38:47-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +88 / -1 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

A construction whose initializer is the resolver-synthesized
memberwise init compiled as: allocate a blank record, call the init,
SetField per field. The blank was aliased across the caller and init
frames during the call, so IsUnique never passed and every SetField
copy-on-wrote the whole field vector — the convention defeated its
own CoW (measured at 7.6% of pure-VM time; 600k constructions cost
600k calls, 1.2M SetFields, and 1.2M vector clones on the VM
benchmark). Such constructions now take the existing direct path —
one Record instruction with the arguments in field order. Detection:
the synthesized body carries Span::SYNTHESIZED, guarded by exact
param/field arity so user inits and default-valued fields keep the
call path; 'heap constructions keep it too (their ObjectSet region
merging is load-bearing). Memberwise parameters all consume
(ADR 0018), matching the direct path's ownership handling exactly.

VM benchmark: 3.04G -> 1.96G native instructions (-35%), 0.25s ->
0.18s. talk-syntax suite: ~0.75s -> ~0.69s. Shape test pins the
lowering (no blank, no init call); all gates green: 969 workspace,
18 core, 225 talk-syntax, 1 talk-html.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+21/-1): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+67/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `tests/talk_tests.rs` | 67 | 0 |
| `src/backend/mir.rs` | 21 | 1 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn assert_parity_program(name: &str) {`
- `fn memberwise_constructions_build_directly`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (34s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `memberwise_constructions_build_directly`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - lowering (no blank, no init call); all gates green: 969 workspace,

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
