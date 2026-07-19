# Commit 071: `5329de53` - Close every remaining Required ledger row (group B)

| Field | Value |
|---|---|
| Commit | `5329de53d541ed0f686a2f5225b718de5a0b9b9a` |
| Parent reviewed | `ab86dd902efc2bac9e2057147221334c57512953` |
| Author date | 2026-07-16T09:32:47-07:00 |
| Author | Pat Nakajima |
| Patch size | 9 files, +1034 / -63 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

Each row lands from a failing black-box test:

- TOOL-08 tests: package-aware `talk test` compiles suites against the
  locked dependency graph (bodies via DriverConfig::libraries).
- IO-02: `'io(request)` performs dispatch on the request tag straight to
  the runtime's host operations (files, sockets, poll, sleep,
  environment); the request enum's declaration order maps one-to-one
  onto the runtime operation table.
- DYN-01/02: existential coercions pack payloads behind fixed-slot
  witness tables (0 drop, 1 retain, requirements from 2, the archived
  convention); `any P` member calls, drops, and retains dispatch through
  the table.
- OWN-03: strict-linear values must be consumed exactly once on every
  finite path; implicit drop points raise compile errors, and a match
  consumes its linear scrutinee (CHG-07's whole-aggregate rule).
- BOR-03/CHG-04: borrowed returns of a frame's own named owned bindings
  are rejected (the loan would escape its owner). CHG-05 is documented
  as vacuous under one-shot resumption with no mutable borrows.
- TOOL-10: `talk mir` renders the middle representation.

[Commit body truncated here; the patch inventory below is based on the complete diff.]

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 9.
- Production Rust: 6 files (+792/-48): `src/backend/lower.rs`, `src/backend/mir.rs`, `src/backend/mod.rs`, `src/bin/talk.rs`, `src/compiling/driver.rs`, `src/compiling/package.rs`.
- Tests and test oracles: 1 files (+180/-1): `tests/talk_tests.rs`.
- Documentation and plans: 2 files (+62/-14): `docs/backend-parity-ledger.md`, `docs/lean-rebuild-wave-reports.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 517 | 31 |
| `tests/talk_tests.rs` | 180 | 1 |
| `src/compiling/package.rs` | 99 | 0 |
| `src/bin/talk.rs` | 79 | 4 |
| `src/backend/lower.rs` | 58 | 11 |
| `docs/lean-rebuild-wave-reports.md` | 39 | 0 |
| `docs/backend-parity-ledger.md` | 23 | 14 |
| `src/compiling/driver.rs` | 28 | 2 |
| `src/backend/mod.rs` | 11 | 0 |

### Representative declarations touched

- `impl Lowering<'_> {`
- `pub(crate) enum Inst {`
- `pub(crate) struct Program {`
- `fn render`
- `fn needs_drop_inner(builder: &ProgramBuilder<'_>, ty: &Ty, borrowed: bool) -> bo`
- `fn borrow_classified`
- `fn is_linear`
- `enum Glue`
- `struct ProgramBuilder<'a> {`
- `impl<'a> ProgramBuilder<'a> {`
- `fn value_glue`
- `fn protocol_requirements`
- `fn requirement_symbol`
- `fn is_io_effect`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn deferred_error`
- `fn finish`
- ...and 24 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (15s).
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `package_run_and_test_use_the_locked_graph`, `run_performs_ambient_io_operations`, `mir_and_bytecode_inspection_render`, `run_rejects_escaping_borrowed_returns`, `run_enforces_strict_linear_consumption`, `run_executes_existential_values`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 916 workspace tests pass; backend at 5,020 production lines

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

Acceptable within the branch sequence. No commit-local changes are requested.
