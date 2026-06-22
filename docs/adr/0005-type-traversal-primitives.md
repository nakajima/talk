# ADR 0005: Shared traversal primitives for the type representation

## Status

Accepted; implemented. ADR 0004 — the `solve/` module split and the
solver-local dedup — is also implemented; the solver walks this ADR targets
live in named submodules, and the occurs trio is factored through one
`occurs_var` helper. Line references here are against that post-0004 tree.

## Implementation notes

A first pass produced three deviations from the plan. On review they were
*smells*, not essential complexity, and each was resolved — three design
refinements the original plan missed:

1. **One matcher, after fixing arm order (Gap 3).** The plan assumed one
   matcher; a naive merge produced two, because the GADT matcher skipped a
   `Var` actual (`(_, Var) => true` fired before the `Param` arm) while
   conformance binding must bind a rigid `Param` *to* the receiver's
   unification variable — merging broke `extend ... where T == Int`. The real
   difference was only **arm ordering**: putting the `Param` arm before the
   `Var` wildcards makes one `match_pattern` serve both — GADT refinement,
   conformance binding (`bind_param_pattern`), and associated-type collection
   (`collect_assoc_bindings`, filtered). The other apparent differences
   (occurs check, consistency-on-rebind, validation) were just the conformance
   copies being *sloppier*; the unified matcher is stricter and so safer.
   Pinned by `match_pattern_binds_a_rigid_param_to_a_unification_variable` and
   the nested-coverage test.

2. **Top-down normalize fits after splitting `fold_children` out of `fold_ty`
   (Gap 1).** `normalize_deep`/`normalize_check_ty` are a normalize-fixpoint
   (normalize a node, recurse, re-normalize a reduced `Proj`), not a
   leaf-override rebuild. Rather than leave them duplicating the arms, `TyFold`
   now separates `fold_children` (the structural arms, the one owner) from
   `fold_ty` (per-node dispatch, defaulting to `fold_children`). A top-down
   transform overrides `fold_ty` to act before/after recursing and calls
   `fold_children` for the arms. Both normalizers are now `TyFold` impls
   (`Normalizer` in `generate.rs`, `CheckNormalizer` in `lower/mod.rs`); no
   walk re-encodes the arms.

3. **The store-aware query is `pub(crate)`, not `solve`-private (Gap 2).** The
   real smell was a store-aware `Ty` walk needed in both `solve` and
   `generate`. `query_resolved` and its node enum are now `pub(crate)`, and
   `group_owned_roots` (in `generate.rs`) uses them alongside
   `ty_mentions_params` and `ty_has_unresolved`. The node enum was renamed
   `Node → TyNode` so it does not shadow the AST `crate::node::Node`. The
   row/effect-tail policy stays in each closure (deliberately): the walks
   genuinely differ — `ty_mentions_params` ignores row *var* tails while
   `ty_has_unresolved` counts them — so that is essential, not accidental.

Two walks remain hand-rolled, both because a fold is genuinely the wrong shape
(essential complexity, not smells):

- `occurs_and_adjust_*` (`solve/unify.rs`) mutates variable levels as it
  searches (Rémy ranks); its per-variable step is already shared via
  `occurs_var`.
- `rewrite_ty_from_givens_inner` (`solve/givens.rs`) returns a trace
  (`Option<Symbol>`), rewrites against given equalities as a fixpoint, and —
  critically — forks its `seen` set *per child* (`rewrite_child`) so sibling
  occurrences of one type are each rewritten. A `TyFold` carries shared state
  across siblings, which would under-rewrite; the forking is load-bearing, so
  this walk keeps its own recursion.

## Context

An audit of every structural walk over the type representation (`Ty`, `Row`,
`EffectRow`, `Predicate`, `Scheme`) across `src/` found that the same
"descend into `Nominal`/`Func`/`Tuple`/`Record`/`Any`/`Proj`, plus row/effect
tails" recursion is hand-written roughly a dozen times, in six files. This is
the root cause behind ADR 0004's symptoms, but it is **not** a solver problem —
it spans the whole `types`/`lower` tree. It deserves its own decision because
the fix (shared primitives on the data type) is orthogonal to where any one
walk happens to live.

### What primitives already exist

Three generic, closure-driven traversals exist on `Ty` (and delegate from
`Row`/`Predicate`), and `generate.rs` already uses them:

- **`Ty::try_visit`** (`ty.rs:231`) — read-only preorder search-fold with
  `ControlFlow<B>` short-circuit. Also `Row::try_visit` (`ty.rs:73`),
  `Predicate::try_visit` (`ty.rs:196`). Callers: `generate.rs:5320, 5333,
  5351, 5362, 5404, 5417`.
- **`Ty::try_zip`** (`ty.rs:261`) — read-only lockstep walk over two types.
  Also `Row::try_zip` (`ty.rs:84`). Callers: `generate.rs:403, 459`.
- **`Ty::substitute`** (`ty.rs:310`) — the one rebuilding walk, but hardwired
  to param→type substitution (with row-tail splicing). `Predicate::substitute`
  and `Variant::instantiate` are thin wrappers over it.

Documented limitation: `try_visit`/`try_zip` deliberately do **not** descend
into row/effect *tails* (`ty.rs:228–230`). Callers that care about tail params
inspect them separately (e.g. `generate.rs:5355`). Any new primitive must make
an explicit, consistent choice here.

### The gaps, and the walks each gap forces to be hand-rolled

**Gap 1 — no generic owned map/rebuild (`Ty -> Ty`).** `substitute` is the
only rebuild and it is single-purpose, so every other rebuilding walk re-types
the full nine-arm match. Confirmed instances:

- `Ty::import_symbols` / `Row` / `EffectRow` / `Predicate` / `Scheme`
  (`ty.rs:462, 521, 505, 537, 566`) and `TypeCatalog::import_as`
  (`catalog.rs:169`, ~240 lines) — symbol remapping;
- `Ty::sanitize_for_export` (`ty.rs:601`) — `Var→Error`, open tails→rigid;
- `render_ty` (`ty.rs:750`) — `Ty -> String` (a fold to a different result);
- store-aware rebuilds: `VarStore::zonk_ty` (`solve/var_store.rs:123`),
  `Generalizer::quantify_ty` (`solve/generalize.rs:113`),
  `Solver::rewrite_ty_from_givens_inner` (`solve/givens.rs:13`),
  `Generator::normalize_deep` (`generate.rs:5076`);
- post-solve, catalog-only: `Lowering::normalize_check_ty` (`lower/mod.rs:3834`).

That is ~9 copies of the same arm structure. (`Lowering::map_ty`,
`lower/mod.rs:3984`, maps `Ty -> TyId` into a *different* IR and is a
legitimately separate target — a fold to a foreign result type, not a
same-type rebuild.)

**Gap 2 — no store-aware visit.** `try_visit` walks raw structure with `&self`
and cannot resolve unification variables. Walks that must `shallow`-resolve
per node therefore hand-roll the search:

- `Solver::ty_mentions_params` + `row_`/`eff_`/`predicate_`/`constraint_`/
  `var_value_` siblings (`solve/implication.rs:170` and the family above it) —
  escape checking;
- `Solver::ty_has_unresolved` (`solve/unify.rs:213`);
- `Generator::group_owned_roots` (`generate.rs:5037`);
- the search half of `occurs_and_adjust_ty` (`solve/unify.rs:253`, now reading
  each variable through the `occurs_var` helper at `solve/unify.rs:238`).

These also need the row/effect *tails* that `try_visit` skips, so the
store-aware variant must visit tails (or take a flag).

**Gap 3 — no one-way structural match.** The "match a pattern type against an
actual, binding `Param`s into a map" shape is hand-rolled three times, **with
two inconsistencies** — variant coverage *and* binding policy:

- `bind_param_pattern` (`solve/pattern.rs:10`) — handles
  `Nominal/Func/Tuple/Param` only; silently ignores `Record/Any/Proj`; binds
  first-wins (`or_insert_with`, no occurs check);
- `collect_assoc_bindings` (`generate.rs:5261`) — same restricted coverage;
- `VariantInstantiation::bind_result` (`variant.rs:59`) — handles **all**
  variants including `Record/Any/Proj`, and binds with an occurs check
  (`variant.rs` `bind_param`/`occurs`).

So the GADT-result matcher covers cases the other two silently drop, and uses a
stricter binding rule. That is a latent correctness gap, not just duplication.
Note this is *not* a use of `try_zip`: matching is one-way (a `Param` pattern
matches any actual), whereas `try_zip` requires both sides to share shape and
fails the moment they differ.

### Dead code

`Ty::map` (`ty.rs:377`) and `Ty::map_into` (`ty.rs:381`) are named like fold
combinators but are just `f(self)` with no descent, and have **zero call
sites** (confirmed twice; the `map_into!` at `lib.rs:57` is an unrelated
iterator macro). Delete them — they actively mislead, since they suggest a
mapping primitive exists.

### Out of scope / excluded

- `occurs_and_adjust_*` (`solve/unify.rs:253–320`) both searches *and* mutates
  variable levels (Rémy ranks); it is neither a pure visit nor a pure map.
  Only its search half could share Gap 2's primitive (via `occurs_var`); the
  level mutation stays hand-rolled.
- The `Predicate`/`Constraint` split is intentional (ADR 0001 / OutsideIn(X));
  not a traversal concern.

## Research basis

The general technique — one generic traversal over an algebraic data type,
specialized per use by a leaf function, replacing per-use boilerplate
recursions — is established:

- Lämmel and Peyton Jones, *Scrap Your Boilerplate: A Practical Design Pattern
  for Generic Programming* (TLDI 2003): the canonical treatment of generic
  one-layer traversal combinators (`gmapT` for transformation, `gmapQ` for
  queries) that collapse hand-written recursion over large data types into leaf
  functions. Maps directly onto Gap 1 (map/rebuild = `gmapT`) and Gap 2
  (query = `gmapQ`).
- Meijer, Fokkinga, and Paterson, *Functional Programming with Bananas,
  Lenses, Envelopes and Barbed Wire* (FPCA 1991): catamorphisms/folds as the
  principled recursion scheme; `render_ty` and `map_ty` (the fold-to-foreign-
  result cases) are catamorphisms.
- The existing `try_visit`/`try_zip` are already this pattern applied to the
  query and zip cases; this ADR completes it for the map case and the
  store-aware case.

These two papers are not yet mirrored under `papers/`; add them when this ADR
is accepted, per the repo convention.

## Decision

Complete the traversal-primitive set on the type representation and migrate the
hand-rolled walks onto it, incrementally and test-guarded. Order chosen so each
step proves the primitive against code that already has callers and tests
before anything new depends on it.

### Proposed designs

**Gap 1 — a rebuilding fold (`TyFold`).** A one-layer rebuild that owns the
structural arms (and head symbols) once; each walk overrides only the leaves it
transforms. Default methods recurse and rebuild identically, so a walk that
touches only `Param` writes only `fold_param`.

```rust
// in ty.rs
pub trait TyFold {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(v)   => self.fold_var(*v),
            Ty::Param(s) => self.fold_param(*s),
            Ty::Nominal(s, args) =>
                Ty::Nominal(self.fold_symbol(*s), args.iter().map(|a| self.fold_ty(a)).collect()),
            Ty::Func(ps, r, e) => Ty::Func(
                ps.iter().map(|p| self.fold_ty(p)).collect(),
                Box::new(self.fold_ty(r)),
                self.fold_eff(e),
            ),
            Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| self.fold_ty(i)).collect()),
            Ty::Record(row)  => Ty::Record(self.fold_row(row)),
            Ty::Any { protocol, assoc } => Ty::Any {
                protocol: self.fold_symbol(*protocol),
                assoc: assoc.iter().map(|(s, t)| (self.fold_symbol(*s), self.fold_ty(t))).collect(),
            },
            Ty::Proj(b, p, a) => Ty::Proj(Box::new(self.fold_ty(b)), self.fold_symbol(*p), self.fold_symbol(*a)),
            Ty::Error => Ty::Error,
        }
    }
    fn fold_var(&mut self, v: TyVar) -> Ty { Ty::Var(v) }
    fn fold_param(&mut self, s: Symbol) -> Ty { Ty::Param(s) }     // Param -> Ty (substitute needs this)
    fn fold_symbol(&mut self, s: Symbol) -> Symbol { s }          // head rename (import needs this)
    fn fold_eff(&mut self, e: &EffectRow) -> EffectRow { e.clone() }
    fn fold_row(&mut self, r: &Row) -> Row { /* default: recurse fields, keep tail */ }
}
```

This is expressive enough for every Gap-1 walk: `substitute` overrides
`fold_param`/`fold_eff`/`fold_row` (tail splicing); `import_symbols` overrides
`fold_param`+`fold_symbol`+tails; `sanitize_for_export` overrides
`fold_var`/tails; the store-aware `zonk_ty`/`quantify_ty`/`normalize_deep`/
`rewrite_ty_from_givens_inner` hold their `&mut VarStore`/catalog state in the
implementor and override `fold_var`/`fold_eff`/`fold_row`. `render_ty` and
`map_ty` (foreign result types) are *not* migrated — they are catamorphisms to
`String`/`TyId`, a separate `fold` with an associated result type if ever
wanted.

**Gap 2 — a store-aware query.** The read-only dual: resolve through `shallow`
at each node and, unlike `try_visit`, visit tail params too.

```rust
// in solve/var_store.rs (needs &mut VarStore for shallow)
pub(super) enum Node<'a> { Ty(&'a Ty), RowTailParam(Symbol), EffTailParam(Symbol) }

impl VarStore {
    pub(super) fn query_resolved<B>(
        &mut self,
        ty: &Ty,
        f: &mut impl FnMut(&mut Self, Node<'_>) -> ControlFlow<B>,
    ) -> ControlFlow<B> { /* shallow, visit, recurse incl. tails */ }
}
```

`ty_mentions_params` becomes a `Break(symbol)` on
`Node::Ty(Ty::Param(s)) | RowTailParam(s) | EffTailParam(s)` when `s ∈ params`;
`ty_has_unresolved` a `Break(())` on `Node::Ty(Ty::Var(_))`;
`group_owned_roots` a `Continue` that pushes roots; the search half of
`occurs_and_adjust_ty` already isolates its per-variable step in `occurs_var`.

**Gap 3 — one shared one-way matcher.** Extract `bind_result`'s full-variant
logic into a single free fn and route all three sites through it:

```rust
/// One-way structural match: bind every `Param` in `pattern` to the aligned
/// part of `actual`. Single source of truth for pattern binding; covers all
/// `Ty` variants. Returns false on a head mismatch.
pub(crate) fn match_pattern(pattern: &Ty, actual: &Ty, bindings: &mut FxHashMap<Symbol, Ty>) -> bool
```

Reconcile the binding policy explicitly: `bind_result` occurs-checks while
`bind_param_pattern` is first-wins. The shared fn should adopt the
occurs-checked rule (the safe one) unless a caller is shown to depend on
first-wins; that reconciliation is the behavioral decision of this step.

### Steps

1. **Delete dead `Ty::map` / `Ty::map_into`.** Trivial, removes a misleading
   API.
2. **Add `TyFold`** and re-express the *raw* rebuilds first — `substitute`,
   `import_symbols`, `sanitize_for_export` — since they have callers and tests,
   so this validates the primitive.
3. **Migrate the store-aware rebuilds** (`zonk_ty`, `quantify_ty`,
   `rewrite_ty_from_givens_inner`, `normalize_deep`, and catalog-only
   `normalize_check_ty`) onto `TyFold`. These are the bulk of the duplication.
4. **Add `query_resolved`** and migrate `ty_mentions_params` & family,
   `ty_has_unresolved`, `group_owned_roots`, and the search half of
   `occurs_and_adjust_ty`.
5. **Unify the three one-way matchers** into `match_pattern`, adopting
   `bind_result`'s full variant coverage and a reconciled binding policy. This
   step changes behavior (closes the coverage gap), so it gets its own tests
   first.

Steps 1–4 are behavior-preserving refactors. Step 5 is a bug fix with a test
that would have caught the coverage gap.

## Verification

- `cargo test` green after each step.
- Steps 2–4: the migrated walks are covered by existing tests (substitution via
  scheme instantiation throughout `types_tests.rs`; zonk/normalize via solver
  tests; escape via `implication_rejects_escape_*`). Add a `TyFold` identity
  test (folding with all-default leaves returns an equal type) to pin the
  primitive itself.
- Step 5: add tests first — a pattern/actual pair over `Record`, `Any`, and
  `Proj` that must bind correctly, demonstrating the pre-fix `bind_param_pattern`
  drops them; plus a recursive pattern that exercises the occurs check.
- Track lines removed vs added; this ADR should produce a clearly negative
  diff (≈9 rebuild copies and ≥4 query copies collapsing to leaf functions).

## Consequences

- A change to the `Ty` representation touches one primitive plus a handful of
  leaf functions instead of a dozen full recursions across six files.
- The `Record/Any/Proj` binding inconsistency (and the binding-policy
  divergence) is closed.
- Cost: the store-aware primitives must thread `&mut VarStore` through the
  implementor, slightly more intricate than the `&self` `try_visit`; and the
  tail policy must be chosen once (`TyFold::fold_row`/`fold_eff`,
  `query_resolved` visiting tails) and applied consistently.
- Builds directly on ADR 0004: the solver's store-aware walks now live in named
  submodules (`solve/var_store.rs`, `solve/givens.rs`, `solve/generalize.rs`,
  `solve/implication.rs`, `solve/unify.rs`), so each migration is a localized
  change to one file.
