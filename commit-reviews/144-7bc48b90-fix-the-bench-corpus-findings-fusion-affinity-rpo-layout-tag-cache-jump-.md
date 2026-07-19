# Commit 144: `7bc48b90` - Fix the bench-corpus findings: fusion, affinity, RPO layout, tag cache, jump threading

| Field | Value |
|---|---|
| Commit | `7bc48b90e50f53c881461328754d2a89b53062ed` |
| Parent reviewed | `be16cf9f72ffa26508e9b1707892ca7c4a878ae7` |
| Author date | 2026-07-18T00:23:49-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +526 / -55 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Four of the five findings from reading the benchmark bytecode, each
pinned by bench_bytecode_is_tight:

Assignment fusion (regalloc): `inst t = ...; Copy v <- t` where t
dies at the copy rewrites the producer to write v directly — `i =
i + 1` is one instruction again, removing the two per-iteration
moves that were 20% of every scalar loop body. Sound by adjacency:
the VM reads operands before writing destinations. Never-read copy
destinations (a loop statement's discarded Unit) delete outright.

Affinity groups (regalloc): the single last-wins register hint
becomes union-find groups over every copy pair and Goto edge pair
(the coalescing structure of George & Appel, TOPLAS 1996, applied to
hints), so a two-predecessor join coalesces with both its arguments;
parameters claim their group's register up front and expire into the
free pool at their last use (fib's base case now returns r0
directly, zero moves in the whole function). Reservations exist only
for groups of two or more, and a fresh register beats stealing one.

Reverse-postorder block layout (regalloc): the builder allocates
join blocks before compiling arms, so a join's linear interval
falsely covered its predecessors and coalescing was denied. Blocks
now lay out in RPO (successors visited in reverse so then-arms land
before else-arms), with Goto/Branch/unwind block ids remapped.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 4.
- Production Rust: 3 files (+439/-55): `src/backend/lower.rs`, `src/backend/mir.rs`, `src/backend/regalloc.rs`.
- Tests and test oracles: 1 files (+87/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/regalloc.rs` | 304 | 50 |
| `src/backend/lower.rs` | 101 | 0 |
| `tests/talk_tests.rs` | 87 | 0 |
| `src/backend/mir.rs` | 34 | 5 |

### Representative declarations touched

- `fn lower_function(`
- `fn thread_and_compact`
- `fn thread_and_compact_once`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn successors(block: &BlockData) -> Vec<usize> {`
- `fn fuse_adjacent_copies`
- `fn layout_blocks`
- `pub(crate) fn reuse_locals(function: &mut Function) {`
- `fn find_group`
- `fn adjacent_assignment_copies_fuse_into_their_producer`
- `fn bench_corpus_runs() {`
- `fn bench_bytecode_is_tight`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (40s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `adjacent_assignment_copies_fuse_into_their_producer`, `bench_bytecode_is_tight`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - suite runs 5.81G native instructions (was 6.03G). All gates green:

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
