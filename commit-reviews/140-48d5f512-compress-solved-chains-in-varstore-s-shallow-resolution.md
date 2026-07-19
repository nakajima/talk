# Commit 140: `48d5f512` - Compress solved chains in VarStore's shallow resolution

| Field | Value |
|---|---|
| Commit | `48d5f512c46c1652113cbd850581af0486f68acf` |
| Parent reviewed | `88489ff70062092948ac23731f0d5cfc78dc40f8` |
| Author date | 2026-07-17T22:00:02-07:00 |
| Author | Pat Nakajima |
| Patch size | 1 files, +70 / -10 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

find() already compressed unsolved union-find paths, but a chain of
solved variables (a bound to Var(b), b bound to Var(c), c bound to a
constructor) re-walked and re-cloned on every query. shallow() now
walks bindings by reference, clones the final constructor once, and
rewrites the entry variable's binding to point straight at it — the
same amortization as Tarjan's path compression (Tarjan, JACM 1975),
applied to the solved half of the store. Rebinding to an equal,
further-resolved value is transparent to every observer, and the
generation counter stays put: compression is not solver progress.

Two unit tests pin the compression and the unsolved-root case.

Also assessed and deliberately not done: sharing Ty's aggregate
payloads (Rc arguments, toward hash-consed types). A probe conversion
of Nominal alone surfaces 94 compile errors (~300 edit points across
all variants), against measured Ty clone+drop traffic of ~6-7% of
compile — roughly 15-20ms of a 750ms run. The checker's 19% share is
dominated by constraint-solving work, not clone traffic; the trade
does not clear the bar. Recorded in the plan.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 1.
- Production Rust: 1 files (+70/-10): `src/types/solve/var_store.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/types/solve/var_store.rs` | 70 | 10 |

### Representative declarations touched

- `impl VarStore {`
- `pub(crate) enum TyNode<'a> {`
- `fn origin`
- `fn shallow_compresses_solved_chains_to_one_hop`
- `fn shallow_of_an_unsolved_root_stays_unsolved`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (37s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `shallow_compresses_solved_chains_to_one_hop`, `shallow_of_an_unsolved_root_stays_unsolved`.
- No test files or executable language test fixtures changed in this patch.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
