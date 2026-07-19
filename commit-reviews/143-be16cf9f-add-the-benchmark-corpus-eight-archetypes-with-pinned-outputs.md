# Commit 143: `be16cf9f` - Add the benchmark corpus: eight archetypes with pinned outputs

| Field | Value |
|---|---|
| Commit | `be16cf9f72ffa26508e9b1707892ca7c4a878ae7` |
| Parent reviewed | `1566a24a2a52bec8569e7fbd5de72127da393b41` |
| Author date | 2026-07-17T23:09:48-07:00 |
| Author | Pat Nakajima |
| Patch size | 18 files, +232 / -0 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

One self-contained program per workload archetype the profiling
passes surfaced: tight scalar loops (arith), struct construction and
field reads (fields), enum match dispatch (dispatch), call machinery
(calls/fib), UTF-8 grapheme iteration (strings), Array growth and
bounds-checked reads (arrays), per-iteration ownership traffic
(drops), and resumable effects (effects). Each prints one
deterministic value; bench_corpus_runs pins the outputs and leak
fences. bench/README.md maps archetypes to their dominant opcodes
and documents the analysis workflow (talk mir / talk bytecode /
talk build + run-image under perf).

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 17, M: 1.
- Tests and test oracles: 1 files (+48/-0): `tests/talk_tests.rs`.
- Language sources and benchmark fixtures: 16 files (+153/-0): `bench/arith.tlk`, `bench/arrays.tlk`, `bench/calls.tlk`, `bench/dispatch.tlk`, `bench/drops.tlk`, `bench/effects.tlk`, `bench/expected/arith.stdout`, `bench/expected/arrays.stdout`, and 8 more.
- Documentation and plans: 1 files (+31/-0): `bench/README.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `tests/talk_tests.rs` | 48 | 0 |
| `bench/dispatch.tlk` | 31 | 0 |
| `bench/README.md` | 31 | 0 |
| `bench/fields.tlk` | 23 | 0 |
| `bench/arrays.tlk` | 18 | 0 |
| `bench/strings.tlk` | 17 | 0 |
| `bench/effects.tlk` | 17 | 0 |
| `bench/drops.tlk` | 17 | 0 |
| `bench/arith.tlk` | 12 | 0 |
| `bench/calls.tlk` | 10 | 0 |
| `bench/expected/strings.stdout` | 1 | 0 |
| `bench/expected/fields.stdout` | 1 | 0 |
| `bench/expected/effects.stdout` | 1 | 0 |
| `bench/expected/drops.stdout` | 1 | 0 |
| `bench/expected/dispatch.stdout` | 1 | 0 |

### Representative declarations touched

- `enum Shape`
- `struct Pair`
- `struct Point`
- `fn assert_parity_program(name: &str) {`
- `fn bench_corpus_runs`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (1s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (35s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `bench_corpus_runs`.
- Added Talk/expected-output fixtures: `bench/arith.tlk`, `bench/arrays.tlk`, `bench/calls.tlk`, `bench/dispatch.tlk`, `bench/drops.tlk`, `bench/effects.tlk`, `bench/expected/arith.stdout`, `bench/expected/arrays.stdout`, `bench/expected/calls.stdout`, `bench/expected/dispatch.stdout`, `bench/expected/drops.stdout`, `bench/expected/effects.stdout`, `bench/expected/fields.stdout`, `bench/expected/strings.stdout`, `bench/fields.tlk`, `bench/strings.tlk`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
