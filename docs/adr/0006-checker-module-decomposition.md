# ADR 0006: Decomposing the constraint generator

## Status

Accepted; implemented. Superseded architecturally by ADR 0007; this ADR remains the record of the generator file split.

## Context

`src/types/generate.rs` is ~5,426 lines. As with the solver before ADR 0004,
the size is a symptom; the structural problem is that one `impl<'a>
Checker<'a>` block (lines 497–5135, ~4,640 lines, ~108 methods) holds the
entire constraint generator — catalog construction, binding-group scheduling,
bidirectional expression/statement/pattern checking, annotation lowering,
solver driving, and finalization — as a single undifferentiated surface.

This ADR is backed by a read of the file. Two facts make decomposition safe
and worthwhile, exactly as for `solve.rs`:

- **The external seam is one function.** `check_types` (`generate.rs:86`) is
  the *only* `pub` item, with a single caller (`driver.rs:451`). Nothing else
  in the file is reachable from outside. `Checker`, its ~30 fields, and all
  ~108 methods are private. So a module split is low-risk provided
  `check_types` stays re-exported from `crate::types::generate`.
- **The coupling is method-call, not data.** Every method mutates the same
  `Checker` fields through `&mut self` (the `VarStore`, `TypeCatalog`,
  `wanteds`, the `ret_stack`/`eff_stack`/`self_types`/`binder_stack` context
  stacks, the output maps). Splitting one `impl` across files (Rust permits
  this for one type within a module) needs only `pub(super)` visibility bumps,
  no data restructuring.

### Verified inventory

Line ranges below were read from the file. The `Checker` impl clusters
cleanly by concern:

| Concern | Lines | Representative methods |
|---|---|---|
| Orchestration | 497–749 | `run`, `check_matches` |
| Catalog collection | 750–1576 | `register_struct`/`_enum`/`_protocol`/`_effect`/`_extend`, `lower_requirement`, `collect_type_aliases` |
| Bounds & declared predicates | 1577–1828 | `register_*_bounds`, `declared_predicates`, `lower_where_clause_predicates` |
| Extend / protocol defaults | 1829–2026 | `check_extend`, `check_protocol_default` |
| Solver driving & binding groups | 2027–2646 | `run_solver`, `solve_deferred`, `check_group`, `finalize` |
| Expressions (bidirectional) | 2647–3226 | `infer_expr`/`check_expr`, `infer_expr_kind`, match checking |
| Calls & construction | 3227–3537 | `finish_call`, `infer_member_call`, `infer_construction`, `resolve_type_member` |
| Functions / closures / blocks | 3538–3831 | `infer_func`, `infer_callable`, `infer_closure_block`, `*_block_value` |
| Statements & local decls | 3832–4004 | `infer_stmt`, `check_local_decl` |
| Patterns | 4005–4307 | `check_pattern`, `check_variant_pattern` (+ `PatternRefinement`, 271–496) |
| Scope & instantiation | 4308–4520 | `lookup`, `with_binder`, `instantiate`, `instantiate_variant*` |
| Type & annotation lowering | 4521–5029 | `lower_type_alias`, `lower_nominal_path`, `lower_annotation`, object-safety checks |
| Finalization helpers | 5030–5135 | `join`, `final_ty`, `normalize_deep` (`Normalizer`), `zonk_predicate`, `emit_*` |
| Free-fn helpers | 5156–5426 | `binding_groups`, `head_symbol`, `collect_*params`, `*_mentions_*` |

Genuine entanglement points (to become `pub(super)` across files): the context
stacks (`ret_stack`, `eff_stack`, `self_types`, `binder_stack`, `with_binder`)
are touched by most clusters; `run_solver`/`emit_eq`/`emit_eff_eq` and the
finalization helpers are called from nearly everywhere; `instantiate` and the
lowering helpers are called from expressions, calls, and patterns alike. None
of this is data coupling — it is the inference engine sharing one mutable
context, which a split preserves unchanged.

### What this ADR does NOT change

- No behavior change and no algorithm change — pure code movement.
- The free-fn helpers that already ride ADR 0005's traversal primitives
  (`ty_mentions_param`, `collect_ty_params`, etc. via `try_visit`) stay as-is;
  any further dedup is out of scope here.
- The `Normalizer` (`TyFold`, from ADR 0005) moves with the finalization
  helpers; no change.

## Research basis

The module boundaries follow the structure the generator already implements
from published work (mirrored under `papers/`).

- Jones, *Typing Haskell in Haskell* (2000), §11.6: type inference is staged —
  build the environment, split top-level binders into dependency-ordered
  binding groups, infer each group, then generalize. This is the seam between
  the *collection*, *binding-group*, and *finalization* modules
  (`run`/`check_group`/`finalize`).
- Dunfield and Krishnaswami, *Bidirectional Typing* (ACM CSUR 2021): the
  paired `infer_*` / `check_*` judgements (`infer_expr`/`check_expr`,
  `infer_func`/`infer_func_against`, `check_pattern`) are bidirectional rules.
  Grouping each syntactic category's infer/check pair in one module mirrors the
  rule structure.
- Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann, *OutsideIn(X)* (JFP
  2011): generation accumulates wanteds and hands them to the solver per group
  (`run_solver`), with floated constraints re-solved at the end
  (`solve_deferred`). The generation/solving boundary is the module boundary
  between this file's `groups` cluster and `solve/` (ADR 0004).

## Decision

### Level 1 — module split (no behavior change)

Convert `generate.rs` to a `src/types/generate/` directory. `Checker`, its
fields, the entry `check_types`, the small work-list structs, and `run` stay in
`mod.rs`; each cluster moves to its own file as a separate `impl<'a>
Checker<'a>` block with `pub(super)` visibility where needed.

```
src/types/generate/
  mod.rs           check_types, Checker struct + fields, work structs, run/check_matches, re-exports
  collect.rs       register_struct/_enum/_protocol/_effect/_extend, requirement & type-alias collection
  bounds.rs        generic/func/where bounds, declared_predicates, where/protocol predicate lowering
  extend.rs        check_extend, check_protocol_default
  groups.rs        run_solver(_with), report_unresolved_residuals, solve_deferred, check_group, finalize
  expr.rs          infer_expr/check_expr, infer_expr_kind, match checking
  call.rs          finish_call, infer_member_call, infer_construction, resolve_type_member
  func.rs          infer_func/_callable/_against, closures, block values
  stmt.rs          infer_stmt, check_local_decl
  pattern.rs       PatternRefinement, check_pattern, check_variant_pattern, refinement equalities
  instantiate.rs   lookup/with_binder, instantiate(_variant), record_*, apply_type_args
  lower_ty.rs      type-alias & nominal-path lowering, lower_annotation/any, object-safety checks
  finalize.rs      join, ambient_eff, group_owned_roots, final_ty, normalize_deep (Normalizer), zonk_predicate, emit_*
  support.rs       free fns: binding_groups, head_symbol, collect_*params, *_mentions_*, decl_kind_name
  tests.rs         (if any unit tests live in-file today)
```

Re-export `check_types` from `mod.rs` so `driver.rs` keeps importing
`crate::types::generate::check_types`. Target: no file over ~800 lines (the
catalog-collection and expression clusters are the largest cohesive units and
may stay near that).

Risk: low (pure movement; one public entry). Move one cluster per commit; run
`cargo test` after each.

### Level 2 — optional follow-up (separate, not required here)

Once split, two cleanups become localized and reviewable, but are explicitly
*not* part of the split:

- The four near-identical `register_struct`/`register_enum` substitution and
  member-collection preludes may share helpers (to be confirmed post-split).
- `infer_expr_kind` (~260 lines) is a large dispatch `match`; arms could move
  to per-construct helpers if any prove independently testable.

These are noted so the split's file sizes are understood, not committed to.

## Verification

- `cargo test` green after every cluster move.
- The split has no dedicated unit tests today; `types_tests.rs` (integration
  over the whole checker) and the full suite are the safety net. Because the
  change is pure movement behind one public function, a green suite is
  sufficient evidence.
- Track lines moved vs added: Level 1 ≈ 0 net (movement + `impl` wrappers and
  `use super::*;` headers).

## Consequences

- Each inference phase becomes independently readable; new language work (GADTs
  per ADR 0002, existentials per ADR 0003) lands in the relevant module instead
  of the monolith.
- Pairs with ADR 0004: `generate/` and `solve/` then mirror each other —
  generation and solving each a directory of phase-named files over one shared
  context type.
- Cost: a one-time large file-move diff, and ~30 `Checker` methods gaining
  `pub(super)`.
