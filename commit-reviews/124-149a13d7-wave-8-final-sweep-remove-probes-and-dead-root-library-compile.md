# Commit 124: `149a13d7` - Wave 8: final sweep — remove probes and dead root-library compile

| Field | Value |
|---|---|
| Commit | `149a13d75d74bd51da53db97686fb3d4f2fde12b` |
| Parent reviewed | `6cb99c995905ba946d690678ca1e1a502dfb9a39` |
| Author date | 2026-07-17T13:33:10-07:00 |
| Author | Pat Nakajima |
| Patch size | 3 files, +19 / -57 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

The five TALK_BACKEND_DEBUG eprintln probes were session scaffolding;
gone. compile_graph compiled and stored the root library, but both
call sites (binary and test) deliberately re-parse root sources into
their own compile and read only the dependency map — the field was
never read and the compile was dead work. The plan records closure:
all gates green (18 core, 16 frozen, 225+1 external, 16/16 examples,
79 reference pins, flow 170/183, 950 workspace tests).

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 3.
- Production Rust: 2 files (+4/-57): `src/backend/mir.rs`, `src/compiling/package.rs`.
- Documentation and plans: 1 files (+15/-0): `docs/lean-backend-rebuild-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 0 | 41 |
| `src/compiling/package.rs` | 4 | 16 |
| `docs/lean-backend-rebuild-plan.md` | 15 | 0 |

### Representative declarations touched

- `impl<'a> ProgramBuilder<'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `struct CompiledGraph {`
- `impl PackageProject {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (39s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- No test files or executable language test fixtures changed in this patch.
- Author-reported validation (not independently treated as proof for the exact commit):
  - all gates green (18 core, 16 frozen, 225+1 external, 16/16 examples,
  - 79 reference pins, flow 170/183, 950 workspace tests).

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
