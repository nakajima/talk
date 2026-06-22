# ADR 0004: Decomposing the constraint solver

## Status

Accepted; implemented.

## Context

`src/types/solve.rs` is ~3105 lines. The size is a symptom; the structural
problem is that one `impl<'s> Solver<'s>` block (lines 376–2428, ~2050 lines)
fuses every phase of the algorithm into a single surface, so a reader cannot
see where one phase ends and the next begins.

This ADR is backed by a full audit of the file and its callers (see
*Verified inventory* below). Two facts make the decomposition safe and
worthwhile:

- **The external seam is tiny.** Despite its size, `solve.rs` exposes almost
  nothing. `Solver` has exactly one public method, `solve` (constructed once,
  at `generate.rs:2014`; its `pub` fields are written only at that site).
  Outside `solve.rs` the entire surface used is: `Solver::solve`,
  `Generalizer::{new, generalize}`, the `VarStore` method set, the free fn
  `normalize_ty`, and `pub(crate) bind_param_pattern` (used by
  `lower/mod.rs`). Nothing reaches into `Solver` internals. So a module split
  is low-risk as long as those items stay re-exported under
  `crate::types::solve::`.
- **The coupling is method-call, not data.** Every cluster mutates the same
  `Solver` fields through `&mut self`; the entanglement is which method calls
  which, not shared field layout. Splitting one `impl` across several files
  (Rust permits this for one type within a module) needs only `pub(super)`
  visibility bumps, no data restructuring.

### Verified inventory

Line ranges below were verified by reading the file.

| Concern | Lines | Items |
|---|---|---|
| Variable store | 74–281 | `VarStore`: `fresh*`, `find`, `union`, `bind`, `shallow`, `zonk_*`, `flatten_*`, `render*` |
| Normalization (free fns) | 295–341 | `normalize_ty`, `stuck_projection`, `sorted`, `FlatTail` |
| Solver struct + loop | 343–526 | `Solver`, `solve`, `eq_residual_guard` |
| Implication / escape | 532–721 | `solve_implication`, `escaping_outer_binding`, the `*_mentions_params` family |
| Given rewriting | 723–890 | `rewrite_ty_from_givens*`, `oriented_given_rewrite`, `given_protocols_for`, `given_conformance_satisfies` |
| Conformance / derive | 895–1073 | `try_conforms`, `conforms_via_bounds`, `not_conforming`, `try_derive` |
| Member dispatch | 1084–1572 | `dispatch_member_through`, `try_member` (~310 lines alone), `bind_requirement` |
| Improvement | 1578–1712 | `improve` |
| Scheme instantiation | 1716–1775 | `symbol_ty`, `instantiate_scheme` |
| Unification | 1780–2427 | `unify`, `unify_eff`, `unify_rows`, `occurs_and_adjust_*`, `bind_row_or_report_infinite`, error reporting |
| Generalization | 2430–2646 | `Generalizer`, `quantify_*` |
| `bind_param_pattern` (free) | 2655–2678 | one-way structural match shared with the lowerer |
| Tests | 2680–3105 | `Harness`-based unit tests |

Cohesion is real for the implication/escape, given-rewriting, conformance,
instantiation, and unification clusters. The genuine entanglement points:

- `improve` (improvement) calls `bind_requirement` (member dispatch);
- given-rewriting's `given_mentions_local_params` bridges into escape
  checking's `ty_mentions_params`;
- `bind_requirement` is called from three places (`try_member`,
  `dispatch_member_through`, `improve`), so it must stay broadly visible;
- `normalize_ty`, `rewrite_ty_from_givens`, and `store.render` are called from
  nearly every cluster (they are already module-level free fns / a separate
  type, so this is fine).

`Generalizer` shares only `VarStore` with `Solver` — it moves out with
essentially zero friction.

### Solver-local duplication the audit found

Independent of the module split, the audit found near-verbatim duplication
*within* `Solver` that should be collapsed:

- **`unify_eff` (2085) and `unify_rows` (2239) share one skeleton** — flatten
  both sides, compute `only_a`/`only_b`, define a `mismatch` closure, then
  `match (ta, tb)` over the same nine `(FlatTail, FlatTail)` cases with the
  same touchability logic. They differ only in payload (effect-label set vs.
  fields) and that `unify_rows` additionally unifies shared fields. Verified by
  reading both.
- **The struct-method (1273–1306) and enum-method (1311–1353) arms of
  `try_member`** are near-identical: instantiate substitution, `symbol_ty`,
  `substitute`, then the same `match shallow(signature)` with identical
  `Func`/`Var`/`_` arms. Verified by reading.
- **`occurs_and_adjust_ty`/`_eff`/`_row_var` (1990–2066)** repeat the same
  "find root, compare level, lower if greater" tail block three times.

### What this ADR does NOT touch

The audit's larger finding — the type representation has no generic
map/rebuild or store-aware traversal, so ~9 hardwired structural walks are
duplicated across `ty.rs`, `solve.rs`, `generate.rs`, `variant.rs`,
`catalog.rs`, and `lower/mod.rs` — is a *system-wide* concern, not a solver
one. It is handled separately in **ADR 0005**. The two efforts are orthogonal:
0004 moves code and removes solver-local copy/paste; 0005 introduces shared
primitives the whole `types`/`lower` tree can adopt.

The parallel `Predicate` (ty.rs) / `Constraint` (constraint.rs) enums are
**not** duplication to remove: they are the deliberate OutsideIn(X) split
between origin-free facts and originated, blame-carrying wanteds/givens. Leave
them distinct.

## Research basis

The module boundaries follow the phase structure the solver already implements
from published work (mirrored under `papers/`).

- Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann, *OutsideIn(X)* (JFP
  2011): separates the constraint domain X (unification — `unify`/`unify_eff`/
  `unify_rows`) from the simplifier over wanteds/givens, and gives implication
  constraints their own treatment with touchable variables and escape
  checking. This is the seam between the `unify`, `solve`, and `implication`
  modules.
- Jones, *A Theory of Qualified Types* (ESOP 1992): predicates carry evidence
  and are discharged against assumptions — the basis for the conformance /
  member-dispatch modules.
- Jones, *Simplifying and Improving Qualified Types* (1994): improvement is a
  justified substitution from satisfiability, distinct from solving — the
  basis for keeping `improve` its own module.
- Jones, *Typing Haskell in Haskell* (2000), §11.6: generalization splits
  predicates into deferred and retained and quantifies — the basis for the
  `generalize` module boundary.
- Pottier and Rémy, *The Essence of ML Type Inference* (2005), and Rémy, *Type
  inference for records in a natural extension of ML* (1992; mirrored as
  `remy-1992-...`): levels/ranks on unification variables and the
  occurs-and-adjust traversal justify isolating the variable store as one unit.

## Decision

### Level 1 — module split (no behavior change)

Convert `solve.rs` to a `src/types/solve/` directory. `Solver` stays in
`mod.rs`; each cluster moves to its own file as a separate `impl<'s>
Solver<'s>` block, with `pub(super)` visibility where needed.

```
src/types/solve/
  mod.rs          Solver struct, solve(), eq_residual_guard, re-exports
  var_store.rs    VarStore + fresh/find/union/bind/shallow, zonk_*, flatten_*, render*
  normalize.rs    normalize_ty, stuck_projection, sorted, FlatTail
  implication.rs  solve_implication, escaping_outer_binding, *_mentions_params
  givens.rs       rewrite_ty_from_givens*, oriented_given_rewrite, given_protocols_for
  conformance.rs  try_conforms, conforms_via_bounds, not_conforming, try_derive
  member.rs       dispatch_member_through, try_member, bind_requirement, symbol_ty, instantiate_scheme
  improve.rs      improve
  unify.rs        unify, unify_eff, unify_rows, occurs_and_adjust_*, error reporting
  generalize.rs   Generalizer + quantify_*
  pattern.rs      bind_param_pattern (re-exported as pub(crate))
  tests.rs        existing Harness-based tests
```

Re-export `Solver`, `VarStore`, `Generalizer`, `normalize_ty`, and
`bind_param_pattern` from `mod.rs` so `generate.rs` and `lower/mod.rs` keep
importing from `crate::types::solve::`. Target: no file over ~650 lines.

Risk: low (pure movement; the external seam is the five items above). Move one
cluster per commit; run `cargo test` after each.

### Level 2 — collapse solver-local duplication (removes code)

Done as separate commits, each guarded by an existing or added test:

1. Extract a shared row/effect unification helper that `unify_eff` and
   `unify_rows` both call for the nine `(FlatTail, FlatTail)` cases,
   parameterized by the per-payload difference and the shared-field action.
2. Factor the struct/enum method-dispatch arms of `try_member` into one helper
   taking the resolved `params`/`methods` lookup.
3. Collapse the `occurs_and_adjust_*` trio's repeated tail block.

These need no new cross-module primitive; they are local to the `unify`/
`member` modules.

### Verification

- `cargo test` green after every move (Level 1) and every extraction (Level 2).
- The existing suite is the safety net: the implication-escape tests
  (`implication_rejects_escape_*`), the row/effect unification tests
  (`effect_rows_merge_through_open_tails`, `closed_record_rows_must_match_exactly`,
  `record_row_occurs_check_rejects_cyclic_tail_through_field`), and the occurs
  test (`occurs_check_rejects_infinite_type`) directly cover the Level 2
  targets. Add a focused test before any extraction not already pinned.
- Track lines removed vs added: Level 1 ≈ 0 (movement), Level 2 negative.

## Consequences

- Each OutsideIn(X) phase is independently readable; GADT refinement from ADR
  0002 and existentials from ADR 0003 landed in the relevant modules instead
  of the old monolith.
- Cost: a one-time large file-move diff (Level 1) and care to keep the unify
  and member extractions behavior-preserving (Level 2).
- The cross-cutting traversal cleanup (ADR 0005) becomes easier to land once
  the solver's store-aware walks live in named, single-purpose modules.
