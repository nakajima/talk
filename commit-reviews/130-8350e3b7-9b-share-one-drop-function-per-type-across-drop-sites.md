# Commit 130: `8350e3b7` - 9b: share one drop function per type across drop sites

| Field | Value |
|---|---|
| Commit | `8350e3b7e90245c3d42a6ac29564e6e1c020bbf4` |
| Parent reviewed | `e09a28b7fa9a8baa9a9b34166ed32bc35db1802d` |
| Author date | 2026-07-17T17:59:08-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +156 / -3 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

A type's structural teardown (field walks, enum tag dispatch, Deinit
hook ordering) was macro-expanded at every drop site; on a parser
corpus the dying values are large AST enums, so each site expanded
to dozens of instructions. Ordinary drop sites now emit one call to
the type's Glue::Drop function — the mechanism existential witness
tables already used, renamed shared_drop — so the expansion is
emitted once per program (the per-type `dec` shape — Ullrich & de
Moura, IFL 2019; Perceus, PLDI 2021, presumes it before selectively
re-inlining). Kept inline: trivial drops (single free or region
release, one dropping field), rigid-generic glue (sites hold the
frame witnesses), linear types (their drops are diagnosed at the
site), and heap structs. A shared function's own root value expands
structurally; nested same-type occurrences call the function — real
recursion for recursive types.

New test pins the shape: two functions dropping the same struct and
enum produce exactly one shared body per type, and the program runs
leak-free. talk-syntax suite: 0.98s -> 0.89s (compile 0.43s ->
0.36s). All gates green: 961 workspace, 18 core, 225 talk-syntax,
1 talk-html.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+80/-3): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+76/-0): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 80 | 3 |
| `tests/talk_tests.rs` | 76 | 0 |

### Representative declarations touched

- `impl<'a> ProgramBuilder<'a> {`
- `fn drop_is_shared`
- `struct FunctionBuilder<'p, 'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn assert_parity_program(name: &str) {`
- `fn structural_drops_share_one_teardown_body`
- `enum Wrap`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (37s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `structural_drops_share_one_teardown_body`.
- Existing test surfaces changed: `tests/talk_tests.rs`.
- Author-reported validation (not independently treated as proof for the exact commit):
  - 0.36s). All gates green: 961 workspace, 18 core, 225 talk-syntax,

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
