# Commit 133: `43c6c050` - Wave 10: coalesce copies, bitset liveness, flat alias table, block constants

| Field | Value |
|---|---|
| Commit | `43c6c050a1770efa0ee150afb08de6e1208dc080` |
| Parent reviewed | `aa132b56f983dfb46f6e3ae35fbf80961b9f8136` |
| Author date | 2026-07-17T18:48:38-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +166 / -33 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Four measured fixes from the second profiling pass:

Register coalescing: a Copy whose source interval ends exactly at the
copy hints its destination onto the source's register (register
hints — Wimmer & Mössenböck, VEE 2005), and lowering already elides
dest==src moves — Moves were 29% of all executed VM instructions.
Safe at equal positions because the VM reads an instruction's
operands before writing its destination; hints only ever pair a copy
with its own source, so multi-destination instructions cannot share.

Liveness bitsets: the dataflow fixpoint's per-block FxHashSet<u16>
was the compile's top self-time entry; live sets are now dense u64
words with word-wise union/kill.

Alias table: canonical()'s thread-local FxHashMap became a flat
Vec<u16> indexed by module id — the lookup runs on every tagged
symbol the backend touches.

Block constants: a constant materializes once per block instead of
once per use (Consts were 17% of executed instructions), held in a
block-persistent register band below per-instruction scratch — a
straight-line slice of lazy code motion (Knoop, Ruething & Steffen,
PLDI 1992).

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 3 files (+166/-33): `src/backend/lower.rs`, `src/backend/mir.rs`, `src/backend/regalloc.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/regalloc.rs` | 119 | 23 |
| `src/backend/mir.rs` | 22 | 7 |
| `src/backend/lower.rs` | 25 | 3 |

### Representative declarations touched

- `fn lower_function(`
- `struct Lowering<'a> {`
- `impl Lowering<'_> {`
- `pub(crate) fn canonical(symbol: Symbol, module: crate::compiling::module::Module`
- `pub(crate) fn reuse_locals(function: &mut Function) {`
- `fn copy_chains_coalesce_onto_one_register`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (39s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `copy_chains_coalesce_onto_one_register`.
- No test files or executable language test fixtures changed in this patch.
- Author-reported validation (not independently treated as proof for the exact commit):
  - test pins copy coalescing. All gates green: 963 workspace, 18 core,

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
