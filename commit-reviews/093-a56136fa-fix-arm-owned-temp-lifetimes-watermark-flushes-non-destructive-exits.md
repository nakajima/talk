# Commit 093: `a56136fa` - Fix arm-owned temp lifetimes: watermark flushes, non-destructive exits

| Field | Value |
|---|---|
| Commit | `a56136fa17c249eb4132422fee4f109f3c2ca7cb` |
| Parent reviewed | `233dcc4978f85e4e262287010b6b0039d1b33b59` |
| Author date | 2026-07-17T03:17:55-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +152 / -6 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

Two ownership bugs behind the talk-syntax method_decl family (10 of 16
audit-time failures): statements flushed the whole temp list, dropping
a match arm's owned bindings at the first inner statement boundary
(drop-then-retain, the double frees); and the return path's flush
consumed shared ownership state, so a returning arm erased entries its
sibling arm still needed (the leaks). Statement flushes now stop at
their own watermark, and frame-exit drops read ownership state without
mutating it — the drop_scopes_from discipline. talk-syntax stands at
3 failures (for-loop body arg, two imports).

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 2 files (+58/-6): `src/backend/mir.rs`, `talk-runtime/src/interp.rs`.
- Tests and test oracles: 1 files (+94/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `tests/talk_tests.rs` | 94 | 0 |
| `src/backend/mir.rs` | 39 | 6 |
| `talk-runtime/src/interp.rs` | 19 | 0 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn drop_stmt_temps_for_exit`
- `fn flush_stmt_temps_above`
- `fn run_loop(module: &Module, machine: &mut Machine) -> Result<Value, String> {`
- `fn run_routes_clause_performs_to_outer_handlers() {`
- `fn run_keeps_arm_bindings_across_inner_statements`
- `enum Out`
- `fn run_balances_temps_when_a_sibling_arm_returns`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (17s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `run_keeps_arm_bindings_across_inner_statements`, `run_balances_temps_when_a_sibling_arm_returns`.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
