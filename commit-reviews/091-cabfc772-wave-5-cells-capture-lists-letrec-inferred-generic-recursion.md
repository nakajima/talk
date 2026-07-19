# Commit 091: `cabfc772` - Wave 5: cells, capture lists, letrec, inferred-generic recursion

| Field | Value |
|---|---|
| Commit | `cabfc7721d0f782b2ad91e32c8610c9ce9411b31` |
| Parent reviewed | `40593fdfed0c52254c8cdc92798befea6fa56ec4` |
| Author date | 2026-07-17T02:28:35-07:00 |
| Author | Pat Nakajima |
| Patch size | 9 files, +702 / -142 |
| Review result | **Request changes** |

## Intent and sequence context

Assignment conversion lands on the runtime's dormant cell opcodes: a
symbol assigned anywhere in a frame and referenced under a nested
function value binds through a cell, so the frame and its closures
share one mutable slot (makeCounter, independent counters, top-level
mutation, recursive capturing locals via celled letrec binders — all
reference pins). Capture lists enforce completeness, copyability for
[copy], and move-on-[consuming]; owned-payload modes reject fail-closed
until closure drop glue exists. demand_specialized completes recursive
inferred generics from the enclosing instance's bindings (the static
sub-dictionary rule). The Identity/Show leaks were the return path
never flushing statement temporaries — return now drops chain
intermediates like a tail expression; FileIO/TrailingBlock pins gain
the CLI's trailing-value line over byte-identical reference stdout. G5
is 15/16 pinned; Imports remains. Deepening: capture_env/bind_env are
the one closure-environment contract (wave 6's extension point);
cell_celled_params dedupes; compile_closure drops its dead parameter.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 2, M: 7.
- Production Rust: 2 files (+458/-127): `src/backend/lower.rs`, `src/backend/mir.rs`.
- Tests and test oracles: 6 files (+206/-15): `tests/examples/expected/Capture.stdout`, `tests/examples/expected/Fib.stdout`, `tests/examples/expected/FileIO.stdout`, `tests/examples/expected/Show.stdout`, `tests/examples/expected/TrailingBlock.stdout`, `tests/talk_tests.rs`.
- Documentation and plans: 1 files (+38/-0): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 445 | 127 |
| `tests/talk_tests.rs` | 201 | 14 |
| `docs/lean-backend-rebuild-plan.md` | 38 | 0 |
| `src/backend/lower.rs` | 13 | 0 |
| `tests/examples/expected/FileIO.stdout` | 1 | 1 |
| `tests/examples/expected/TrailingBlock.stdout` | 1 | 0 |
| `tests/examples/expected/Show.stdout` | 1 | 0 |
| `tests/examples/expected/Fib.stdout` | 1 | 0 |
| `tests/examples/expected/Capture.stdout` | 1 | 0 |

### Representative declarations touched

- `impl Lowering<'_> {`
- `pub(crate) enum Inst {`
- `fn free_locals(nodes: &[&Node], enclosing: &FxHashMap<Symbol, LocalId>) -> Vec<S`
- `fn cell_scan`
- `struct Scan`
- `fn enter_expr`
- `fn exit_expr`
- `fn enter_decl`
- `fn exit_decl`
- `fn enter_stmt`
- `fn bind_env`
- `impl<'a> ProgramBuilder<'a> {`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn cell_celled_params`
- `fn check_capture_list`
- `fn demand_specialized`
- `fn capture_env`
- ...and 12 additional declaration contexts.

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (16s): `run_enforces_capture_list_modes`.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `run_shares_mutable_captures_through_cells`, `run_executes_local_functions_that_capture`, `run_enforces_capture_list_modes`, `run_specializes_recursive_inferred_generics`, `run_releases_intermediates_of_a_return_chain`, `run_shares_captured_assignments_with_the_frame`.
- Added Talk/expected-output fixtures: `tests/examples/expected/Capture.stdout`, `tests/examples/expected/Fib.stdout`.

## Findings

### 1. [P1] Return ordinary capture diagnostics instead of tripping the unsupported-error invariant

- Location: `src/backend/mir.rs:5888-5894` and `src/backend/mir.rs:5930-5934` (tip line numbers)
- Status: **Unresolved at branch tip**
- Impact: `BackendError::unsupported` has a debug assertion requiring every message to contain `not supported yet`. Two capture-list rule violations added here do not contain that phrase: copying a non-copyable capture and omitting a free variable from an explicit list. Both paths panic in the debug CLI instead of returning the intended source diagnostic. The integration test added by this commit reaches the omitted-variable path, so the normal debug test suite is red. With `RUST_BACKTRACE=1` the test can falsely pass because the backtrace itself contains the symbol `check_capture_list`, satisfying its broad `stderr.contains("capture")` assertion.
- Evidence: `cargo test --test talk_tests run_enforces_capture_list_modes -- --exact` fails; `cargo test --locked` ends at 90 passed / 1 failed. Piping the test program to `target/debug/talk run` exits 101 at `src/backend/mod.rs:60`.
- Recommended correction: Use `BackendError::new` for semantic rule diagnostics (or include the required unsupported marker only for genuinely unsupported constructs), and assert the rendered diagnostic rather than a broad backtrace-sensitive substring.

## Disposition

Do not merge this commit as currently represented at the branch tip until the unresolved finding above is corrected.
