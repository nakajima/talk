# Commit 092: `233dcc49` - Wave 6: lexical capability capture; port the reference effects suite

| Field | Value |
|---|---|
| Commit | `233dcc4978f85e4e262287010b6b0039d1b33b59` |
| Parent reviewed | `cabfc7721d0f782b2ad91e32c8610c9ce9411b31` |
| Author date | 2026-07-17T02:45:32-07:00 |
| Author | Pat Nakajima |
| Patch size | 39 files, +414 / -66 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

A capability is FindHandler's existing product — the handler clause and
its stack index — evaluated at closure creation instead of at the
perform (Effekt-style; ADR 0011 departure (d)). Closures carry one
(clause, index) per user effect in their resolved row through the
capture_env/bind_env contract; performs route through the captured
capability when the frame has one and dynamic search otherwise, leaving
every existing handler behavior unchanged. The capture pin prints 300.
All 18 of the reference's user-effects tests port as the G6 effects
cluster and pass. assert_corpus_program/assert_corpus_dir merge the
G2/G5/G6 runners into one corpus mechanism.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 36, M: 3.
- Production Rust: 1 files (+93/-23): `src/backend/mir.rs`.
- Tests and test oracles: 37 files (+297/-43): `tests/reference/effects/abort_effect.tlk`, `tests/reference/effects/abort_handler_captures_local.tlk`, `tests/reference/effects/abort_skips_rest_of_scope.tlk`, `tests/reference/effects/abort_two_levels_below.tlk`, `tests/reference/effects/abort_value_as_scope_value.tlk`, `tests/reference/effects/conditional_abort.tlk`, `tests/reference/effects/conditional_resume.tlk`, `tests/reference/effects/effect_normal_path.tlk`, and 29 more.
- Documentation and plans: 1 files (+24/-0): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 93 | 23 |
| `tests/talk_tests.rs` | 72 | 43 |
| `docs/lean-backend-rebuild-plan.md` | 24 | 0 |
| `tests/reference/effects/handlers_in_two_functions.tlk` | 15 | 0 |
| `tests/reference/effects/effectful_closure_in_struct_field.tlk` | 15 | 0 |
| `tests/reference/effects/resume_two_levels_below.tlk` | 14 | 0 |
| `tests/reference/effects/perform_in_expression_position.tlk` | 14 | 0 |
| `tests/reference/effects/effect_normal_path.tlk` | 13 | 0 |
| `tests/reference/effects/abort_value_as_scope_value.tlk` | 13 | 0 |
| `tests/reference/effects/conditional_resume.tlk` | 12 | 0 |
| `tests/reference/effects/conditional_abort.tlk` | 12 | 0 |
| `tests/reference/effects/abort_two_levels_below.tlk` | 12 | 0 |
| `tests/reference/effects/resuming_handler.tlk` | 11 | 0 |
| `tests/reference/effects/repeated_performs_one_handler.tlk` | 11 | 0 |
| `tests/reference/effects/resume_preserves_enclosing_locals.tlk` | 10 | 0 |

### Representative declarations touched

- `struct fields`
- `fn cell_scan(nodes: &[&Node]) -> (rustc_hash::FxHashSet<Symbol>, rustc_hash::FxH`
- `fn bind_env(`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn capability`
- `fn closure_effects`
- `fn compile_closure`
- `struct Wrapper`
- `fn run_prints_scalars_and_strings() {`
- `fn assert_corpus_program`
- `fn assert_parity_program(name: &str) {`
- `fn assert_parity_program`
- `fn assert_corpus_dir`
- `fn reference_effects_cluster_matches_frozen_stdout`
- `fn run_routes_clause_performs_to_outer_handlers() {`
- `fn run_captures_capabilities_lexically`
- `fn examples_corpus_matches_frozen_stdout() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (14s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` reports the trailing space in `abort_handler_captures_local.stdout`; review confirms it is an intentional output byte from `print("caught: ")`, not accidental source whitespace.
- Added or materially introduced Rust test functions detected in the patch: `assert_corpus_program`, `assert_parity_program`, `assert_corpus_dir`, `reference_effects_cluster_matches_frozen_stdout`, `run_captures_capabilities_lexically`.
- Added Talk/expected-output fixtures: `tests/reference/effects/abort_effect.tlk`, `tests/reference/effects/abort_handler_captures_local.tlk`, `tests/reference/effects/abort_skips_rest_of_scope.tlk`, `tests/reference/effects/abort_two_levels_below.tlk`, `tests/reference/effects/abort_value_as_scope_value.tlk`, `tests/reference/effects/conditional_abort.tlk`, `tests/reference/effects/conditional_resume.tlk`, `tests/reference/effects/effect_normal_path.tlk`, `tests/reference/effects/effectful_closure_in_struct_field.tlk`, `tests/reference/effects/expected/abort_effect.stdout`, `tests/reference/effects/expected/abort_handler_captures_local.stdout`, `tests/reference/effects/expected/abort_skips_rest_of_scope.stdout`, `tests/reference/effects/expected/abort_two_levels_below.stdout`, `tests/reference/effects/expected/abort_value_as_scope_value.stdout`, `tests/reference/effects/expected/conditional_abort.stdout`, `tests/reference/effects/expected/conditional_resume.stdout` and 20 more.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
