# Commit 127: `155fbf8d` - Inline small functions and reuse registers: talk test 2.1s -> 1.3s

| Field | Value |
|---|---|
| Commit | `155fbf8d0b0e19a60903c2d0c0973ebd6c18fd8f` |
| Parent reviewed | `c2677e35ca11d1ddbab9dd019ab5d035147f25e4` |
| Author date | 2026-07-17T15:17:10-07:00 |
| Author | Pat Nakajima |
| Patch size | 7 files, +1205 / -30 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Call counting showed the interpreter making 8.6 million calls per
talk-syntax run, a third of them to one-instruction core functions:
`add`, `equals`, `not`, `times`, comparisons. Three fixes:

MIR inlining (backend/inline.rs): single-block primitive bodies
splice straight into their callers (procedure integration —
Scheifler, CACM 1977); small branching bodies (`get`'s bounds check:
cmp, trap, load) splice as blocks with the caller split at the call
site and every return rejoining after it. Candidates are narrow: a
primitive-instruction whitelist, branch/jump/return/trap terminators
only, no calls, no parameter writes — so no unwind edges or effect
machinery can be disturbed. The pass runs to a fixpoint: splicing
`_load` into `get` makes `get` itself a candidate. Calls per run:
8.6M -> 786k.

Register reuse (backend/regalloc.rs): the instruction builder never
recycles a local index, so frames grew with function length — one
chunk needed 48,824 registers, and every call paid an allocation,
fill, and drop of that width. Liveness by backward dataflow (Aho,
Sethi & Ullman 1986, §10.6) then interval assignment with a free
list — linear scan without spilling (Poletto & Sarkar, TOPLAS 1999) —
renumbers locals onto true-width frames; parameters stay pinned for
the calling convention, and unwind cleanup blocks are graph
successors of their call sites. Constant-materialization scratch in
lowering now resets per instruction. Frame widths: median 6, max 37.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 2, M: 5.
- Production Rust: 6 files (+1157/-30): `src/backend/inline.rs`, `src/backend/lower.rs`, `src/backend/mir.rs`, `src/backend/mod.rs`, `src/backend/regalloc.rs`, `talk-runtime/src/interp.rs`.
- Language sources and benchmark fixtures: 1 files (+48/-0): `core/Operators.tlk`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/inline.rs` | 544 | 0 |
| `src/backend/regalloc.rs` | 530 | 0 |
| `talk-runtime/src/interp.rs` | 56 | 22 |
| `core/Operators.tlk` | 48 | 0 |
| `src/backend/lower.rs` | 16 | 3 |
| `src/backend/mod.rs` | 7 | 1 |
| `src/backend/mir.rs` | 4 | 4 |

### Representative declarations touched

- `struct Candidate`
- `fn primitive`
- `fn remap_inst`
- `fn candidate`
- `fn remap`
- `fn inline_small`
- `fn inline_round`
- `fn local`
- `fn int`
- `fn scalar_add`
- `fn caller`
- `fn scalar_call_becomes_the_scalar_instruction`
- `fn branching_bodies_splice_as_blocks`
- `fn param_writing_bodies_stay_calls`
- `fn callee_temporaries_get_fresh_caller_locals`
- `fn lower_function(`
- `struct Lowering<'a> {`
- `impl Lowering<'_> {`
- ...and 23 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (5s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (44s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `scalar_call_becomes_the_scalar_instruction`, `branching_bodies_splice_as_blocks`, `param_writing_bodies_stay_calls`, `callee_temporaries_get_fresh_caller_locals`, `disjoint_temporaries_share_a_register`, `parameters_keep_their_registers`, `value_live_across_a_loop_is_not_reused_inside_it`, `cleanup_only_values_stay_live_across_the_call`.
- No test files or executable language test fixtures changed in this patch.
- Author-reported validation (not independently treated as proof for the exact commit):
  - All gates hold: 960 workspace tests (8 new unit tests over the two

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
