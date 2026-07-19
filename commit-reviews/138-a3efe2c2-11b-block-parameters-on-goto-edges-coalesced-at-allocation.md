# Commit 138: `a3efe2c2` - 11b: block parameters on Goto edges, coalesced at allocation

| Field | Value |
|---|---|
| Commit | `a3efe2c20e673b1fe69950447c2c44d3dcdebb3b` |
| Parent reviewed | `af7f9817778821448b74a577a8c55bf7d88262e1` |
| Author date | 2026-07-17T21:08:24-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +226 / -48 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

The MIR grows block-parameter SSA edges (Appel, SSA is Functional
Programming, 1998): BlockData declares parameters, Term::Goto passes
one argument per parameter, and merge_arms delivers each arm's value
as an edge argument instead of copying into a shared result local —
the join's result is its parameter. Branch stays argument-free by
construction (merged values always route through dedicated arm-block
Gotos), so no critical-edge splitting exists anywhere.

The allocator treats parameters as block-entry definitions in the
liveness equations and interval build, and a Goto argument dying at
its edge hints the parameter onto its register (the SSA
generalization of the copy hint — Wimmer & Franz, CGO 2010), so the
edge move usually lowers to nothing. Residual edges lower as a
parallel copy sequenced so no pending source is overwritten, cycles
broken through one scratch register (Boissinot, Darte, Rastello,
de Dinechin & Guillon, CGO 2009). The inliner remaps parameters and
edge arguments through the same substitution as body locals.

Deferred, recorded in the plan: Braun construction for reassigned
variables and loop carriers (mutable locals remain mutable locals) —
post-RK its payoff is IR uniformity, not measured counts. Unit test
pins edge coalescing; all gates green: 965 workspace, 18 core, 225
talk-syntax, 1 talk-html.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 4.
- Production Rust: 4 files (+226/-48): `src/backend/inline.rs`, `src/backend/lower.rs`, `src/backend/mir.rs`, `src/backend/regalloc.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/regalloc.rs` | 78 | 4 |
| `src/backend/mir.rs` | 44 | 34 |
| `src/backend/lower.rs` | 71 | 2 |
| `src/backend/inline.rs` | 33 | 8 |

### Representative declarations touched

- `fn candidate(function: &Function) -> Option<Candidate> {`
- `fn inline_round(program: &mut Program) -> bool {`
- `fn lower_function(`
- `struct Lowering<'a> {`
- `impl Lowering<'_> {`
- `fn edge_moves`
- `impl MemTy {`
- `pub(crate) enum Term {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn visit_term(term: &mut Term, visit: &mut impl FnMut(Slot, &mut LocalId)) {`
- `fn successors(block: &BlockData) -> Vec<usize> {`
- `pub(crate) fn reuse_locals(function: &mut Function) {`
- `fn edge_arguments_coalesce_onto_block_parameters`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (39s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `edge_arguments_coalesce_onto_block_parameters`.
- No test files or executable language test fixtures changed in this patch.
- Author-reported validation (not independently treated as proof for the exact commit):
  - pins edge coalescing; all gates green: 965 workspace, 18 core, 225

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
