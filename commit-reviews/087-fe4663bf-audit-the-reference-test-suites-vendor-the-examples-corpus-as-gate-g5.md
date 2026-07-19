# Commit 087: `fe4663bf` - Audit the reference test suites; vendor the examples corpus as gate G5

| Field | Value |
|---|---|
| Commit | `fe4663bf797b119cc39d364026d63c211cc582ec` |
| Parent reviewed | `4da3e0603eac772e18b2dea55c77672d52358af7` |
| Author date | 2026-07-17T00:31:55-07:00 |
| Author | Pat Nakajima |
| Patch size | 51 files, +574 / -0 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Full read of the mature compiler's tests (~/apps/talk main, 0.1.62):
220 VM behavior tests, 219 flow/ownership rules, 33 examples with
frozen stdout, frontend suites (ours already a superset). The plan
gains a gap register:

- S1: lexical capability capture — function values must capture their
  creation site's handlers (pinned 300; our dynamic search gives 400).
  A silent semantic divergence in the effects system.
- F1: mutable captures (cells) are reference behavior, pinned by four
  VM tests and an example; the ledger's CHG-06 rejection row is
  superseded.
- F2-F6: record patterns/destructuring, inferred generic functions,
  multi-file scripts, unique types, iteration-mode verification.
- C: the deleted flow checker's 219 rules (NLL liveness, borrow
  provenance, partial moves, capture modes, markers) are the checking
  spec; this backend enforces a small subset and must port or argue
  each divergence.
- V: ~180 architecture-independent VM behavior pins to port.

The examples corpus is vendored (tests/examples + frozen stdout) and
gated by examples_corpus_matches_frozen_stdout with a five-entry
known-failing burn-down list (FileIO, Identity, Show, TrailingBlock,
Imports). 935 workspace tests pass.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 49, M: 2.
- Tests and test oracles: 50 files (+513/-0): `tests/examples/AnonFunc.tlk`, `tests/examples/Array.tlk`, `tests/examples/Capture.tlk`, `tests/examples/ChatClient.tlk`, `tests/examples/ChatServer.tlk`, `tests/examples/Copy.tlk`, `tests/examples/Effects.tlk`, `tests/examples/Exports.tlk`, and 42 more.
- Documentation and plans: 1 files (+61/-0): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `docs/lean-backend-rebuild-plan.md` | 61 | 0 |
| `tests/talk_tests.rs` | 47 | 0 |
| `tests/examples/ForLoop.tlk` | 44 | 0 |
| `tests/examples/ChatServer.tlk` | 37 | 0 |
| `tests/examples/ChatClient.tlk` | 37 | 0 |
| `tests/examples/Graphemes.tlk` | 24 | 0 |
| `tests/examples/Show.tlk` | 21 | 0 |
| `tests/examples/GADT.tlk` | 19 | 0 |
| `tests/examples/expected/ForLoop.stdout` | 18 | 0 |
| `tests/examples/Throwsies.tlk` | 15 | 0 |
| `tests/examples/WebApi.tlk` | 14 | 0 |
| `tests/examples/Protocols.tlk` | 14 | 0 |
| `tests/examples/Struct.tlk` | 13 | 0 |
| `tests/examples/Loop.tlk` | 13 | 0 |
| `tests/examples/Capture.tlk` | 13 | 0 |

### Representative declarations touched

- `struct Thing`
- `enum Expr`
- `enum Maybe`
- `enum NotEver`
- `struct Fizz`
- `struct Buzz`
- `struct Person`
- `struct Dog`
- `fn talk_test_runs_acceptance_projects() {`
- `fn examples_corpus_matches_frozen_stdout`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (8s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `examples_corpus_matches_frozen_stdout`.
- Added Talk/expected-output fixtures: `tests/examples/AnonFunc.tlk`, `tests/examples/Array.tlk`, `tests/examples/Capture.tlk`, `tests/examples/ChatClient.tlk`, `tests/examples/ChatServer.tlk`, `tests/examples/Copy.tlk`, `tests/examples/Effects.tlk`, `tests/examples/Exports.tlk`, `tests/examples/Fib.tlk`, `tests/examples/FileIO.tlk`, `tests/examples/ForLoop.tlk`, `tests/examples/GADT.tlk`, `tests/examples/Graphemes.tlk`, `tests/examples/HelloWorld.tlk`, `tests/examples/Http.tlk`, `tests/examples/Identity.tlk` and 33 more.
- Author-reported validation (not independently treated as proof for the exact commit):
  - Imports). 935 workspace tests pass.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
