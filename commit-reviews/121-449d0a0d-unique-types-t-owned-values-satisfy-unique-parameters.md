# Commit 121: `449d0a0d` - Unique types (*T): owned values satisfy unique parameters

| Field | Value |
|---|---|
| Commit | `449d0a0d205a7432d37637790b07cb014bc07903` |
| Parent reviewed | `183ef7d3fec7312da590ecc594fbcda28895a68c` |
| Author date | 2026-07-17T12:26:06-07:00 |
| Author | Pat Nakajima |
| Patch size | 4 files, +26 / -8 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

The checker's machinery mostly existed: member lookup now strips
Borrow/Unique wrappers to a fixpoint, and the owned-into-unique
absorption fires for arguments arriving through function-type
decomposition (NestedApply), not just direct application. The backend
strips Unique in resolved() - uniqueness is a checking-time qualifier;
the representation is the inner type. Closes F5's two corpus pins.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 4.
- Production Rust: 3 files (+26/-6): `src/backend/mir.rs`, `src/types/solve/member.rs`, `src/types/solve/unify.rs`.
- Tests and test oracles: 1 files (+0/-2): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/types/solve/member.rs` | 10 | 4 |
| `src/backend/mir.rs` | 13 | 1 |
| `src/types/solve/unify.rs` | 3 | 1 |
| `tests/talk_tests.rs` | 0 | 2 |

### Representative declarations touched

- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `struct StripUnique`
- `fn fold_ty`
- `impl<'s> Solver<'s> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (36s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
