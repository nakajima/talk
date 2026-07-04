# Generic effect handlers: design plan

Status: implemented (2026-07-03, same day — direct to the full design,
no unique-label stopgap). Follow-up to ADR 0011, which fenced `@handle`
for generic effects (`effect 'state<T>(value: T) -> T`) with a
diagnostic.

> **Implementation correction (recorded honestly):** the planned
> scoped-label *pairing* (same-label occurrences unify their arguments
> first-match, Koka's discipline) turned out to be wrong for talk:
> because rows here grow purely by unification, first-match pairing
> forcibly unifies `'state<Int> ~ 'state<Bool>` the moment one function
> performs two instantiations — under that discipline duplicates can
> never *form* through inference (in Koka they enter rows through
> handler/mask types, not inference). What landed instead: **entries are
> inert** — effect-row unification takes a multiset difference by
> structural equality (label AND zonked arguments; empty-argument
> entries behave exactly like the old label set) and never unifies
> arguments across entries. Arguments are solved by each perform's own
> signature check; discharge happens only in the `HandleEffect` label
> filter; rejection only at closed rows. Occurrence order plays no role
> at all, so planned departure 3 (order artifacts) vanished. Everything
> else landed as designed below.

## Context

Everything about ADR 0011's capability passing is monomorphic: a
function's row names the effects it performs, `demand` turns each row
entry into one capability parameter with a concrete payload type, and
`@handle` builds one capability closure. Generic effects break the chain
at the representation: **effect rows carry labels, not instantiations**
(`EffectRow.effects: BTreeSet<Symbol>`). A row saying `'state` does not
say `'state<Int>`, so a capability parameter for `'state` has no
determined domain type, one row entry may stand for `'state<Int>` *and*
`'state<Bool>` in the same function, and an `@handle` cannot know which
instantiations its extent sends through its capability.

Two facts make the full design reachable without staging tricks:

- Perform sites already instantiate the effect's generics fresh and
  record the instantiation per node (`generate/expr.rs`,
  `artifacts.instantiations[expr.id]`, zonked at finalize).
- Handler bodies are **already type-checked generically**: the block's
  arguments take the effect's declared parameter types with the generics
  rigid ("the handler sees the rigid parameters — it must be generic
  over them", `generate/stmt.rs`). The language was designed as if one
  handler covers every instantiation; only the pipeline below typing is
  missing.

## Decision

Three pieces, landed in order, each green:

1. **Rows carry instantiations as inert entries.** `EffectRow.effects`
   becomes a multiset of entries `(Symbol, Vec<Ty>)` — duplicate labels
   allowed, canonicalized by stable sort on label. Unification cancels
   structurally equal occurrences and flows the leftovers into tails;
   entry arguments never unify against each other (see the correction
   note above — this is where the implementation diverged from the
   Koka-style pairing this section originally specified). Duplicate
   labels still serve their Koka purpose: unification stays principal
   and terminating without lacks constraints.

2. **`@handle` is label-scoped elimination: it discharges *every*
   occurrence of its label in the extent's row.** The extent is checked
   under a fresh ambient row `?inner`, and the `Handling` site emits a
   new row constraint `HandleEffect { inner, effect, outer }`: when the
   group's solve quiesces, every `effect`-labeled entry surfaced in
   `inner` is discharged (its args must satisfy the effect's declared
   predicates — already emitted at perform sites) and the remaining
   entries plus `inner`'s residual tail flow to `outer`. This replaces
   `Ctx::with_handled_effect` wholesale — non-generic effects are the
   degenerate case (entries with empty args) — and the top-level
   progressive walk uses the same constraint per `@handle` statement.
   One `@handle 'log` therefore covers `'log<Int>` and `'log<String>`
   in one extent; an inner same-effect handler absorbs *all*
   occurrences, so an outer one is dead for that label (matching the
   runtime's nearest-capability-wins exactly).

3. **Lowering materializes one capability per instantiation from a
   handler template.** As landed: `Ctx` carries two maps — `caps:
   (Symbol, Vec<Ty>) → ExprId` for capability VALUES (our own cap
   parameters, exact instantiations) and `cap_templates: Symbol → usize`
   indexing `Lowering::handler_templates` (a `HandlerTemplate` holds the
   install `Ctx` clone — the delimiter — plus the scaffold `Arc` and the
   handler block). A use site — a local perform (its baked
   instantiation, θ-substituted) or a callee row entry (via
   `cap_entries_of(symbol, theta)`, the canonical order shared by
   `demand`, `lower_function`, and every call) — resolves through
   `resolve_cap`: exact value first, else materialize from the label's
   nearest template, memoized by `(template, instantiation)`
   (`materialize_cap`). The handler body lowers per instantiation with
   `theta ∪ {T ↦ Int}` — **exactly the existing generic-function
   specialization machinery**, applied to a handler block, against the
   template's own scaffold. `resolve_callee` now returns the callee θ so
   call sites can substitute row entries. The resumption/delimiter/VM
   story is untouched — materialized caps are ordinary capability
   closures. Verified end to end by
   `tests/programs/{generic_state,generic_two_instantiations}.tlk`, the
   flipped `generic_effect_handlers_lower`, and a bounded-generic
   (`T: Showable`) handler printing three instantiations.

What this deliberately does **not** include: masking/injection (a callee
cannot reach *past* an inner same-label handler — with label-scoped
elimination there is never a live outer occurrence to reach), and
first-class named instances. Both are orthogonal extensions.

## Why not the alternatives

- **Koka-exact single-occurrence elimination** (handler fixes one
  instantiation; multiplicity via nesting): surprising in talk — a
  handler that silently fails to cover some instantiations of its own
  label contradicts ADR 0011's label-keyed capabilities, and handler
  bodies are already typed generically. Rejected on semantics, not
  difficulty.
- **Rank-2 polymorphic capability values**: one cap "for all T" needs
  erased payloads and coercions — a second value-representation regime
  in a deliberately monomorphic λ_G. The template achieves the same
  expressiveness with specialization instead of erasure.
- **Whole-program instantiation collection**: re-grows the deleted
  `collect_abortable`-style side analysis and fights lazy
  monomorphization; rows are the compositional carrier.

## Implementation

Failing tests first at every step.

### Step 1 — checker: scoped rows with instantiated entries

Tests (`types_tests.rs`):
- `effects::generic_effect_row_carries_instantiation` — `func f() {
  'state(42) }`, no handler: `ty_of(f)` renders `! <'state<Int>>`.
- `effects::two_instantiations_coexist_in_a_row` — one function performs
  `'state(1)` and `'state(true)`, no handler: clean, row renders both
  entries (this is the case the dropped stopgap would have rejected).
- Existing `effects::generic_effect_*` cases stay green.

Changes: entry representation + canonical stable sort (`ty.rs`; Eq/Hash
via the canonical form); `fold_eff`/`substitute`/`import_symbols`/
`sanitize`/quantify/instantiate recurse into entry args (quantification
is what makes a generic function's `'state<T>` row specialize per θ);
`unify_eff` pairs same-label occurrences in order, unifies args
pointwise (mirroring `unify_rows`' pointwise-fields step), leftovers to
tails as today; `flatten_eff` concatenates entries head-then-tail
(preserving occurrence order); perform sites join `(symbol,
instantiation vars)` — the vars already in `instantiations[expr.id]`;
render `'state<Int>`; `pattern.rs` compares canonical entries; the
closed-annotation and `UnhandledEffect` paths key on labels, unchanged.
Handlers keep inserting a bare `(effect, [])`-style entry this step
(generic handlers stay fenced); everything currently green stays green.

### Step 2 — checker: `HandleEffect` elimination constraint

Tests:
- `effects::one_handler_covers_two_instantiations` — `func g() '[] {
  @handle 'state { v in continue v }\n 'state(1)\n 'state(true)\n () }`
  → clean (the heart of the feature).
- `effects::inner_handler_absorbs_all_occurrences` — nested same-effect
  handlers: the outer's extent row shows nothing for the label; program
  clean, and (given Step 3) routing goes to the inner.
- `effects::handler_extent_still_delimits` — perform before the
  `@handle` in a `'[]` function still errors (extent boundary intact).
- Re-run the whole Stage-1 (ADR 0011) row suite — discharge behavior
  for non-generic effects must be byte-identical.

Changes: `Handling` checks the rest-of-block under fresh `?inner` and
emits `HandleEffect { inner, effect, outer }`
(`generate/func.rs` walkers, `groups.rs` top-level walk + group
positioning — `handler_positions` gains nothing; the constraint carries
the position's row); solver: process `HandleEffect` after the group's
queue quiesces — flatten `inner`, discharge `effect`-labeled entries,
unify the rest (and the residual tail var) into `outer`; re-queue if
processing surfaced new row content, then residual-float like other
constraints. `Ctx::with_handled_effect` is deleted. The extent's
`?inner` tail is private to the extent (only constraints generated
inside it can grow it), so group-solve-end is a sound flush point; the
final defaulting solve re-flushes any floated ones.

### Step 3 — lowering: capability templates

Tests:
- Flip `lower_tests::generic_effect_handlers_are_diagnosed` to assert
  success.
- `tests/programs/generic_state.tlk` — `effect 'ask<T>(x: T) -> T`,
  handler `{ v in continue v }`, an unannotated callee performing at
  Int; print. Both engines.
- `tests/programs/generic_two_instantiations.tlk` — one extent, one
  handler, callees performing `'ask(1)` and `'ask("s")`; a generic
  `probe<T>` specialized at both under the same handler.
- VM parity: generic resumable perform in expression position; abort
  variant (`-> Never` generic payload).

Changes (`src/lower`): `CapEntry::{Value, Template}`; templates store
the rebased install `Ctx`, scaffold ids, and effect symbol;
materialize-on-demand memoized by `(template-instance, θ-key)`, lowering
the handler scaffold with `ctx.theta` extended by the effect generics
(straight reuse of `lower_sub_body_from_scaffold` + theta
substitution); `effect_caps_of` returns `(Symbol, Vec<CheckTy>)` entries
(θ-substituted; a row may yield several per label); `cap_dom_items`
takes the args and substitutes `sig.generics`; `demand`/`lower_function`
key cap params by (label, args-signature) in sorted order;
`lower_call`/perform sites resolve each needed (label, args) from
`ctx.caps`; eta-expansion (`eta_expand_effectful_value`) iterates the
same entry list. Delete the three generics fences
(`diagnose_unsupported_handlers`, `lower_mir_handling`,
`cap_dom_items`). Never-effect placeholder resumptions and the VM are
untouched.

### Step 4 — docs

ADR 0011: generic effects implemented; record the label-scoped
elimination as an amendment (it also supersedes departure (b)'s
"same-effect nesting resolved positionally in lowering" — the types now
say the same thing the caps do). `core-ir-map.md` effects note likewise.

## Citations

- **Duplicate labels / ordered occurrence matching for principal row
  unification**: Leijen, *Koka: Programming with Row-polymorphic Effect
  Types* (MSFP 2014) — effect rows with duplicated labels (⟨exn,exn⟩ ≠
  ⟨exn⟩) give principal, terminating unification without lacks
  constraints, and carry parameterized effects like `st<h>` whose
  arguments unify on label match
  ([arXiv](https://arxiv.org/abs/1406.2061),
  [MSR](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/koka-effects-2013.pdf));
  Leijen, *Extensible Records with Scoped Labels* (TFP 2005) — the
  underlying discipline, already cited in `ty.rs` for record rows.
- **Handler typing as row elimination**: Leijen, *Type Directed
  Compilation of Row-Typed Algebraic Effects* (POPL 2017,
  [MSR](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/algeff.pdf))
  — `handle` removes an occurrence from the row. Our elimination is
  label-scoped (all occurrences), a flagged departure below.
- **Generic handler clauses under monomorphizing capability passing**:
  Brachthäuser, Schuster & Ostermann, *Effekt* (JFP 2020,
  [Cambridge](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/effekt-capabilitypassing-style-for-type-and-effectsafe-extensible-effect-handlers-in-scala/A19680B18FB74AD95F8D83BC4B097D4F))
  — capabilities carry the effect's types; operations may be generic and
  the handler implements them generically. The capability template is
  this idea under whole-program specialization.
- **Rank-2 evidence (rejected alternative)**: Xie & Leijen, *Generalized
  Evidence Passing for Effect Handlers* (ICFP 2021,
  [DOI 10.1145/3473576](https://dl.acm.org/doi/10.1145/3473576)).
- **Named instances (orthogonal future)**: Xie, Cong, Ikemori & Leijen,
  *First-class Names for Effect Handlers* (OOPSLA 2022,
  [DOI 10.1145/3563289](https://dl.acm.org/doi/10.1145/3563289)).
- **Runtime contrast**: Sivaramakrishnan et al., *Retrofitting Effect
  Handlers onto OCaml* (PLDI 2021) — `type _ Effect.t` resolves the
  instantiation dynamically at the handler's GADT match; talk resolves
  it statically per materialized capability.

**Novel departures, flagged:**
1. **Label-scoped elimination** (`HandleEffect` filters *every*
   occurrence of the label): no published row system does this — Koka
   eliminates one occurrence, keeping outer same-label handlers
   reachable (with masking). Justified by talk's semantics: capabilities
   are label-keyed, nearest wins for the whole label (ADR 0011), and
   handler bodies were always typed generically. Consequence accepted:
   nested same-label handlers make the outer dead for that label —
   worth a checker warning later.
2. **Capability templates** (per-instantiation specialization of a
   handler *statement*'s closure): a direct composition of Effekt-style
   generic operations with talk's demand-driven monomorphization; no
   direct literature analogue as a compilation unit.
3. **Same-label occurrence order as unification artifact only**: since
   elimination is label-scoped, occurrence order never affects routing —
   it exists purely to keep unification principal (Koka's order is also
   semantic). Programs accumulating same-label entries in different
   orders on two paths can fail to unify (Koka shares this corner).

## Risks / open questions

- **`HandleEffect` solve timing** is the hard part: it must run after
  the extent's row content has surfaced but before generalization reads
  the enclosing function's row. Group-solve quiescence is the flush
  point; the residual/deferred machinery (`report_unresolved_residuals`,
  `solve_deferred`) is the template. A missed re-queue shows up as a
  false `UnhandledEffect` — tests in Step 2 cover the nesting and
  late-tail cases.
- **Cap-param explosion**: a function performing k instantiations takes
  k cap params — fine (mirrors k distinct effects); determinism needs a
  stable (label, args) ordering; reuse `theta_key`-style rendering.
- **Unannotated generic payloads** (`effect 'e<T>(v)` with `v`
  unannotated): payload var and generic interact; keep the existing
  "annotate the effect declaration" diagnostic when a payload survives
  as a var.
- **Template captures**: the stored install `Ctx` must stay valid for
  the whole extent lowering (it does — same `Lowering` session, and
  materialized closures capture the same frame values the eager cap
  did); memoization must key on the *handler instance*, not just the
  effect, or two same-effect handlers in one function would share caps.
- **Predicates on effect generics** (`effect 'log<T: Showable>`): the
  perform sites emit the obligations today; handler-body givens come
  from the declaration's predicates — verify with a bounded-generic test
  in Step 2.
