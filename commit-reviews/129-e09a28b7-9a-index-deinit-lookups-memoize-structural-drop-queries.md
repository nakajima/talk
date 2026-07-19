# Commit 129: `e09a28b7` - 9a: index Deinit lookups, memoize structural drop queries

| Field | Value |
|---|---|
| Commit | `e09a28b7fa9a8baa9a9b34166ed32bc35db1802d` |
| Parent reviewed | `d31a88a970cb23e0b608fc82d6387fdd8353aa17` |
| Author date | 2026-07-17T17:53:23-07:00 |
| Author | Pat Nakajima |
| Patch size | 1 files, +81 / -34 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

deinit_witness scanned every program's whole conformance map per
nominal drop, canonicalizing every key on the way (measured 18.9% of
compile inclusive); is_deinit_witness did the same scan per compiled
callable. Both now read canonical indexes built once in
ProgramBuilder::new, alongside the struct/enum/conformance indexes.
needs_drop, contains_buffer, and contains_object memoize per type —
drop emission asks them per field per site and the answers depend
only on the fixed catalogs.

talk-syntax suite: 1.29s -> 0.98s wall (compile 0.68s -> 0.43s).
All gates green: 960 workspace, 18 core, 225 talk-syntax, 1
talk-html.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 1.
- Production Rust: 1 files (+81/-34): `src/backend/mir.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 81 | 34 |

### Representative declarations touched

- `fn let_bound_func(decl: &Decl) -> Option<(&Name, &Func)> {`
- `fn needs_drop(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {`
- `fn donates(builder: &ProgramBuilder<'_>, ty: &Ty) -> bool {`
- `struct ProgramBuilder<'a> {`
- `struct DeinitRow`
- `impl<'a> ProgramBuilder<'a> {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (39s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- No test files or executable language test fixtures changed in this patch.
- Author-reported validation (not independently treated as proof for the exact commit):
  - All gates green: 960 workspace, 18 core, 225 talk-syntax, 1

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
