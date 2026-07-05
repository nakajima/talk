# Effect parameters on struct types: design plan

Status: designed, not yet implemented. The deficit is pinned by
`types_tests::struct_closure_field_rows_contaminate_across_constructions`
(flip its assertion when this lands). Follow-up to ADR 0015's ledger
entry "Effect-generic closure storage".

## The disease, concretely

A closure-typed field's arrow (`struct Wrapper { let f: () -> Int }`)
gets ONE effect-row variable when the catalog collects the struct. Every
construction in the module unifies its closure's row into that single
variable:

```talk
struct Wrapper { let f: () -> Int }
effect 'ping() -> Void

func pure_use() -> Int {
    let w = Wrapper(f: func() { 1 })
    w.f()                       // ERROR: No handler for 'ping (!)
}
func pingy_use() 'ping -> Int {
    let w = Wrapper(f: func() { 'ping()  1 })
    w.f()
}
```

`pure_use` fails because `pingy_use`'s construction contaminated the
shared row. Across the module boundary the tail becomes an owner-keyed
rigid param freshened per use — which is the OPPOSITE unsoundness
(per-read freshening decouples the read row from what construction
stored; an effect could escape its handler).

## The design (Koka-style kinded type argument)

The instance's row must TRAVEL IN THE TYPE — any side channel
reintroduces one of the two failure modes above. So struct (and later
enum) types take effect-row parameters, instantiated per construction
and substituted at member reads, exactly like type params ride today.

Precedent: Koka's kind system (rows are `E`-kinded type arguments to
constructors, Leijen MSR-TR-2013-79 §4); Frank/Eff pass ability rows as
datatype indices the same way. The nearest existing pattern in-tree:
`Row::Var` wrapped as `Ty::Record(_, Row::Var)` by `collect_metas` —
this design does it properly with a dedicated variant.

1. **Representation**: new `Ty::Eff(EffectRow)` variant, kind-restricted
   by convention to Nominal-argument position (and substitution
   payloads). `TyFold::fold_children` routes it through the existing
   `fold_eff`; unification `Ty::Eff(a) ~ Ty::Eff(b)` delegates to
   effect-row unification (multiset difference, generic-effects rules).
   Blast radius: ~22 exhaustive `match ty` sites across 14 files
   (ty.rs, solve/{var_store,conformance,givens,mod,member,unify},
   generate/{elaborate,collect,call}, flow/{loans,grades},
   analysis/completion, types_tests).

2. **Collection** (`CatalogBuilder`): after lowering a struct's field
   types, scan them for free effect-row tail vars. Each distinct var
   becomes an implicit rigid effect param (synthesized symbol), recorded
   in a new `StructInfo.eff_params: Vec<Symbol>`, and the field tails
   rewrite to `EffTail::Param(sym)`. (Explicit surface syntax can come
   later; inference-only covers the Map/Wrapper cases.)

3. **Construction** (`infer_construction`, call.rs): alongside `theta`
   (fresh var per `info.params`), mint a fresh OPEN row per
   `info.eff_params` (`EffectRow { effects: [], tail: Var(fresh) }`).
   `self_ty = Nominal(symbol, theta ++ eff_rows.map(Ty::Eff))`. The init
   signature substitutes through the eff map — `Ty::substitute` already
   takes an effect-substitution parameter, so the plumbing exists. Each
   construction gets its own row: contamination gone.

4. **Annotation lowering**: a user-written `Wrapper` (annotations never
   name eff params) appends one fresh row var per `eff_params` entry in
   inference position; in declared signatures they generalize into the
   enclosing scheme's `eff_params` (machinery exists —
   `quantify_leftover_eff_vars`).

5. **Member/field reads**: nominal member dispatch already binds
   `info.params` against the receiver head's args; extend the zip to
   bind `eff_params` against the trailing `Ty::Eff` args as an effect
   substitution. The read now sees the INSTANCE's row — sound in both
   directions.

6. **Conformances / self_args**: heads written as `extend Wrapper<T>`
   have no eff mention; conformance head binding (`bind_param_pattern`
   and friends) must tolerate/bind the `Ty::Eff` suffix — bind them as
   row wildcards (any instance row conforms) unless a future syntax
   constrains them.

7. **Erasure at HIR build**: capability-passing already carries a
   stored closure's caps in its env (ADR 0011), so eff args are
   runtime-irrelevant. Strip `Ty::Eff` args from `Nominal` when baking
   node types (the same place `As`/`RowVariable` erase), so flow,
   lowering, and specialization keys never see them. Typing keeps them
   internally; `sanitize_for_export` handles leftover tails via the
   existing owner-keyed minting (automatic through the fold).

## Order of implementation (each slice compiles + suite green)

1. `Ty::Eff` variant + fold/unify/substitute/render/serde arms (inert —
   nothing constructs it yet).
2. `StructInfo.eff_params` + collection rewrite of field tails.
3. Construction appends eff args + substitutes; annotation lowering
   appends fresh rows; well-formedness arity updated.
4. Member-read eff binding; conformance-head tolerance.
5. HIR-build erasure of `Ty::Eff` args.
6. Flip the pinned test; add: cross-module store/read soundness test
   (effectful closure stored, read elsewhere, handler still required),
   and a Map-shaped generic-struct test (`struct Map<K,V>` with a
   closure field, two instantiations with different rows).

## Risks / open questions

- Coordination: `types/generate/*` and `solve/*` are under active
  concurrent edit (var_store origin work) — land slice 1 when the tree
  is quiet.
- Enum payloads with closure types have the same disease; the design
  extends (`Enum.eff_params`), but v1 scopes to structs.
- Rendering: `Ty::Eff` in diagnostics should print as a row (`'e`), not
  as a pseudo-type.
