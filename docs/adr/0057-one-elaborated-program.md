# ADR 0057: One elaborated program

Status: DRAFT (challenge me). Umbrella for ADR 0053 (one catalog: facts),
ADR 0054 (one adaptation judgment: value crossings), and ADR 0055
(unforgeable blame: locations) — this ADR names the principle those three
are instances of, applies it to the remaining axes, and locks it in place
so the disease cannot regrow.

History: a full rewrite of `src/types` + `src/compiling/mir` was considered
(2026-08-11) and rejected. The architecture is not the problem — OutsideIn(X)
generation/solving and the CFG builder are the right frames and would be
re-derived as-is; the recurring bugs come from duplicated judgments and
re-derived facts, which a rewrite reproduces under schedule pressure and a
refactor can delete. The deciding asymmetry: the algorithms sit behind
narrow seams and are replaceable piecemeal, while `ty.rs`/`catalog.rs` are
the compiler-wide vocabulary — a rewrite that touches them is a
whole-compiler rewrite, and one that doesn't is this ADR done all at once
without a green suite between lands.

## The disease

ADR 0038 unified MIR's re-derivations (19 slices). ADR 0053 unified catalog
facts. The 2026-08-09 sweep was still "entirely seam bugs", and ADR 0054's
table lists eight live copies of the adaptation judgment. Unification
passes keep winning battles while the war regrows, because three standing
invitations to duplicate survive each pass:

**1. Judgments live as methods on phase state, so they are not callable
where the next author needs them.** `solve_adapt` (`solve/mod.rs:497`)
needs `&mut Solver` and defers on `Ty::Var`; generation code has neither a
solver nor patience, so it grew eager twins
(`emit_immediate_argument_eq`/`emit_immediate_borrow_check` in
`generate/expr.rs`, `push_immediate_argument_eq` in `solve/member.rs:1999`
— line-for-line the same match, written twice because one pushes to
`self.wanteds` and the other to a `queue` parameter). The copies have
already diverged: `push_apply_param_eq` (`solve/unify.rs:452`) peels
`Ty::Unique`; its generation-side twins never mention it. Nobody *chose*
duplication — calling was impossible from their context. A judgment that
is not a pure function over data will be copied by every phase that
cannot reach it.

**2. Seams are conventions, not boundaries.** `TypedProgram` exposes
`types()` and `resolved_names()` (`typed_program.rs:54`, `:58`), so any
lowering site can fall back to re-asking the raw tables — and does
(`mir/build/mod.rs` reads `types().` 7 times and `resolved_names()` 3
times beyond the sanctioned per-instance `resolved()`). Everything lives
in one crate, so `pub(crate)` reaches everywhere and nothing fails to
compile when a phase re-derives what an earlier phase already decided.
The typed tree itself documents the halfway state: `typed_ast` bakes
`ty` onto every expression "so downstream stages read it here instead of
a NodeID-keyed table" — while `TypeOutput::node_types` still exists and
the tree copies from it. A fact with two homes is ADR 0053's disease,
reintroduced by the migration that was meant to cure it.

**3. Per-node facts are lookups, so they are partial by construction.**
`TypeOutput` (`src/types/output.rs:266`) is the catalog plus ~20 side
tables, 15 of them `FxHashMap<NodeID, _>`. A lookup can miss, and a miss
invites the consumer to re-derive locally or fail silently:
`solve/member.rs:919` discharges a `HasMember` with `?` when a scheme is
absent (constraint dropped, no error); ADR 0055's audit found the same
shape for locations. The 100+ `BackendError::unsupported` gates in
`mir/build` and `types/generate` are largely this too — paths that could
not reach a fact and punted rather than re-derive it wrongly.

**Tests cannot hold this line.** A fresh copy of a judgment fails no test
— it passes the same suite its original passes, until it diverges. Tests
pin behaviors; they cannot express "this module is not allowed to decide
that." The only checker in the build that can express architectural
soundness is `rustc` itself: visibility and the crate DAG are verified on
every compile. The cure moves the invariants there.

## The cure

**A phase publishes its decisions as data that later phases can read but
cannot mint; realizers realize and are forbidden — by visibility, not
policy — from judging; the boundary is a crate, so a violation is a build
failure, not a review finding.**

Four mechanisms, each deleting one invitation:

### 1. A judgment is a pure function in a module that owns its rules

The rule ADR 0054 already states, plus the seal that keeps it true: the
judgment module (`types/adapt.rs`) owns the tier tests (the
`Shared`/`Exclusive` comparisons today hand-copied at four sites, the
borrow peeling, the `Ty::Unique` peel) as private helpers. Its public
surface is `adapt(found, expected, site) -> Adapted | Deferred | Error`
where `Adapted` is a read-only evidence value — private field, public
`kind()` accessor — so downstream code can realize an adaptation it was
handed but cannot fabricate one it wasn't. Callable from generation,
solving, and finalize alike because it takes data, not `&mut Solver`;
eager-vs-deferred becomes the *caller's* posture around one rule instead
of two implementations of the rule.

### 2. The program artifact is an elaborated tree, not an annotated one

Finish what `typed_ast` started, and delete the tables it was started to
delete. Every per-occurrence decision becomes a field on the typed node —
present by construction, not resolvable by lookup:

- already baked: `ty`, clone facts, member resolution;
- to bake: `instantiations`, `witness_layouts`, `selected_callables`,
  `integer_literals`, `existential_packs`, `checked_ir`,
  `effect_contracts`, `pattern_tys`, `struct_pattern_slots`,
  `record_pattern_slots`, adaptation evidence (mechanism 1), and the
  narrowing spans ADR 0055 wants;
- consumed at emission, never published: `for_plans` and
  `propagation_plans` guide the builder's own `For`/`?` lowering and die
  as tables.

The sorting rule is crisp: **NodeID-keyed per-occurrence decisions become
tree fields; Symbol-keyed program facts live in the one catalog** (ADR
0053's axis — `schemes`, `display_names`, conformance rows stay where
they are). `TypeOutput` shrinks to the catalog plus the program-level
residue (`schemes`, `synthetic_floors`, `display_names`), and
`TypedProgram::types()` / `resolved_names()` are deleted: MIR and the
LSP read the elaborated tree and the catalog, full stop. A fact a
consumer needs and cannot find is a missing field — a compile error at
the consumer — not a silent `None` at runtime.

### 3. A seam is a crate

Extract the front end (`parsing`, `name_resolution`, `desugar`,
`macro_expansion`, `types`, `typed_ast`, shared diagnostics) into
`talk-front`, whose public API is: parse/check entry points, the
elaborated program, catalog views, and diagnostics. `mir/build`, the
driver, the CLI, and `analysis/` stay in the root crate. After this,
"MIR consults checker internals" and "a new module re-derives a
resolution" stop being review findings and become unbuildable — the
same enforcement that has kept the `talk-mir` seam clean since ADR 0047
(three backends, zero violations, because Cargo refuses them). For the
residue visibility cannot express (in-crate discipline, e.g. banning the
raw coerce-tier query outside `adapt.rs`), workspace `clippy.toml`
`disallowed-methods`/`disallowed-types` entries make CI red at compile
time — a build gate, not a test.

### 4. Where a doer and a checker coexist, both read one computed model

The pattern `release::plan`/`verify` already prove: they share one
fixpoint (`verify::entry_states`, `release.rs:78`), so they cannot
disagree. Generalize it to the rest of the ownership analysis, per
`docs/ownership.md`'s unfinished design: the flow facts the builder
hand-threads today (`moved`, `use_counts`, `loans`, `borrow_roots`,
`invalidated_views`, `view_locals`, `uninitialized`, `moved_globals`,
`anchored_closures`, `captured_locals`, and the hand-written
`merge_arms` join at `mod.rs:3999`) become outputs of one dataflow pass
over the built CFG. Lowering emits and records events (it already does:
`FlowEvent`); the pass computes states; borrow/use diagnostics, drop
planning, and the balance verifier all read the same states. "Every
future construct is a fresh chance to forget a merge" (ownership.md)
stops being true because there is no per-construct merge to forget.

## What this makes impossible

| violation | today | after | enforced by |
|---|---|---|---|
| re-implement an adaptation tier | 8 sites, 1 diverged | rule private to `adapt.rs`; evidence unmintable | visibility + lint (slice 1) |
| lowering re-derives a typing decision | `types()`/table reads in `mir/build` | accessors deleted; decision is a tree field | compile error (slice 2) |
| a per-node fact is missing at realization | silent `None` / local re-derivation / `unsupported` | field exists or the node doesn't | construction (slice 2) |
| new module reaches checker internals | one crate, `pub(crate)` everywhere | `talk-front` boundary | Cargo (slice 3) |
| new construct forgets a flow merge | 10+ hand-threaded builder fields | states computed from the CFG | one fixpoint (slice 4) |
| copies of module-level facts | solved | solved | ADR 0053 |
| fabricated diagnostic location | in flight | in flight | ADR 0055 `Blame` |

## What stays

- The checker's architecture: constraint generation/solving, binding
  groups, levels, the catalog. This ADR moves *where results live*, not
  how they are computed.
- The `talk-mir` seam and all three adapters (ADR 0047) — untouched.
- The balance verifier — it keeps auditing, now against states it shares
  with the planner and the diagnostics instead of a parallel replay.
- The corpus, the differential C sweep, the bootstrap fixed point — the
  gates every slice lands through.
- ADR 0007's advice ("do not pursue more separation of checker
  internals") — compatible: this ADR seals the checker's *output*, it
  does not decompose its internals further.

## The plan: four slices

Four, deliberately. Every land is an opportunity for drift — a halfway
state where a fact has two homes or a judgment two owners is exactly the
disease — so each slice runs to a state with **one** owner before it
stops, even where that makes the slice large. Fewer than four would bundle
independent authorities (value crossings, program facts, the crate lock,
flow) into lands too big to review or bisect; more than four would
reintroduce the two-homes interregnums that 0054's five-stage plan
accepts. Every slice lands green through the full gate: workspace suite,
reference corpus under `TALK_CHECK_ALL=1`, differential C sweep (gcc +
clang), bench pins, `talk bootstrap` fixed point.

### Slice 1 — one adaptation judgment, sealed

ADR 0054's remaining stages (2–5), landed as one change on top of the
stage-1 draft (change #3: `TypeCatalog::donate_kind`,
`Solver::record_donation`), plus the seal 0054 doesn't specify:

- `adapt` as a pure function in `types/adapt.rs`; tier tests and borrow
  peeling private to the module; `Adapted` evidence read-only.
- Delete the generation-side twins, `push_apply_param_eq` /
  `push_borrow_downgrade_eq` / `push_immediate_argument_eq`, the
  finalize twins, and the `ApplyBorrow`/`CoerceOwned` constraint forms.
- One MIR realizer consulted by all five call-lowering paths; the
  Identity-double-free regression test becomes its contract test.
- One adaptation diagnostic; message re-pins in the same land.
- `clippy.toml`: the raw tier queries disallowed outside `adapt.rs` and
  the catalog.

The `Ty::Unique` divergence is resolved *by decision* here, not
discovered later: the solver-path peel is the correct rule; the
generation twins die rather than get fixed.

### Slice 2 — total elaboration, seam sealed

The checker emits the elaborated tree; the tables die; the accessors die.

- `finalize` + `typed_program/build.rs` fuse: the tree is built once,
  with every per-occurrence table folded into fields per the sorting
  rule above. `for_plans`/`propagation_plans` are consumed during tree
  emission and never published.
- `TypeOutput` shrinks to catalog + program-level residue. Delete
  `TypedProgram::types()` and `resolved_names()`; `mir/build`'s table
  and `ResolvedNames` reads move onto tree fields (the sanctioned
  per-instance `resolved()` keeps its ADR 0038 shape, fed from the
  tree's instantiation fields).
- The elaborated program carries one `NodeID -> node` index for the
  LSP's random access (hover, completion, occurrences). An index into
  the one authority is not a second home — it holds pointers, not
  copies of facts.
- Cache payload changes shape (`(Module, TypedProgram)` is bincoded):
  `FORMAT_VERSION` bumps with it, per the 0053 precedent.
- Each `unsupported` gate that existed because a fact was unreachable
  from lowering either gains its field and its implementation in this
  slice, or is re-justified in place as a genuine semantic rejection —
  none survives as "couldn't see the fact from here."

This is the largest slice. It is one land because its halfway state —
field and table both live, some consumers on each — is the two-homes
state this ADR exists to abolish; the tree's own doc comment is the
fossil of the last time that state was left standing.

### Slice 3 — the crate lock

Extract `talk-front` (parsing, name_resolution, desugar,
macro_expansion, types, typed_ast, common diagnostics). Public API:
frontend entry points, the elaborated program, catalog views,
diagnostics, `Blame` (ADR 0055). The root crate keeps driver, MIR,
backends glue, CLI, REPL, LSP. Mechanical import churn, no logic
change; lands immediately after slice 2 so the boundary freezes the
elaboration wins before further MIR work proceeds. From here the Cargo
DAG is the architecture document, and this ADR's guarantees survive
authors who never read it.

### Slice 4 — computed flow

Finish `docs/ownership.md` inside the sealed boundary:

- One dataflow pass over the built CFG (extending the
  `verify::entry_states` machinery the planner already trusts) computes
  init/move/loan/liveness states per point.
- Borrow and use-after-move diagnostics, `release::plan`, and the
  verifier read the computed states. The ~10 checking fields listed in
  mechanism 4 leave `FunctionBuilder`, along with `merge_arms`.
- The four structural type-walks (`drop_value`/`retain_value`, their
  enum twins, and `glue.rs`'s equality/show emitters) collapse onto one
  member-iteration primitive — same land, since drop glue is being
  retouched anyway.
- Additions that guard the surgery: a ~150-line structural MIR verifier
  (block-param arity vs `Goto` args, terminator presence, id bounds)
  under `debug_assertions` at the publication point, and pinned
  `talk mir --no-opt` goldens for ~20 construct-family programs so
  regressions bisect at the MIR level instead of at "program printed
  the wrong number."

## Why this is also the diet

The line count and the bug class have the same cause: knowledge
represented more than once. Non-test `src/` core today: `types` ~30.1k,
`compiling` ~33.8k. What the slices delete is not padding but second
homes — eager judgment twins, five call paths' worth of consumption
logic, four type-walks, the table-to-tree copying layer, the
import/export/interface machinery 0053 already condemned, ~10 builder
fields and their save/restore ceremony, and the `unsupported` gates that
existed to paper over unreachable facts. Expected steady state for the
semantic core is roughly **45k** (from ~64k), measured, not promised:
every slice reports lines removed vs added in its change description,
and a slice that comes out net-positive (slice 4's verifier and goldens
are additive) must say what it bought. The remaining ~50k of the tree —
VM, formatter, LSP analysis, FFI, wasm, REPL — is priced separately and
is not this ADR's business.

## Risks, resolved in advance

- **Performance.** Field reads replace hash lookups on the hot lowering
  path — strictly cheaper. The elaborated tree is bigger than the AST +
  tables only by its index; bench pins gate every slice, and the LSP
  workspace holds one program either way. The `runs.txt` regression
  ritual (frontend cost is watched here) applies.
- **LSP partiality.** Hover/completion sometimes want facts for nodes in
  files that failed later phases. The tree exists per checked file
  exactly as `TypedProgram.files` does today (blocked files already
  skip); analysis keeps its current degradation shape.
- **Serialization.** Slice 2's cache bump is contained;
  `frontend.tbc`/`frontend.abi` carry no catalog (0053 audit) so
  bootstrap artifacts are untouched except by the routine fixed-point
  re-pin.
- **Slice-2 size.** The land is big but monotone: one table at a time
  folds into a field with its consumers in the same commit series, and
  the suite is green at the land, not between commits. The 0038 slice
  log shows this exact shape sustained nineteen times; this does it once
  more, wider, and then locks the door (slice 3) so it is the last time.
- **Change #3 is a sibling draft** (parent: change 2). Slice 1 rebases
  or absorbs it; its description's "next in stack" list is this ADR's
  slice 1 scope.

## Citations (per decision)

- **Elaborate into a core where every implicit decision is explicit
  syntax** — GHC's Core/System FC: coercions and dictionaries are terms,
  so later passes transform rather than re-infer
  ([System F with Type Equality Coercions](https://www.microsoft.com/en-us/research/publication/system-f-with-type-equality-coercions/),
  [GHC commentary: Core](https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/core-syn-type)).
- **A fully-typed, desugared tree between checking and lowering** —
  rustc's THIR: "fully typed, hence 'typed HIR'", constructed after
  type checking precisely so MIR building makes no type decisions
  ([rustc-dev-guide: THIR](https://rustc-dev-guide.rust-lang.org/thir.html)).
- **Flow analysis computed over the CFG, not threaded through
  construction** — NLL borrow checking is a dataflow pass over built MIR
  ([RFC 2094](https://rust-lang.github.io/rfcs/2094-nll.html),
  [rustc-dev-guide: MIR borrow check](https://rustc-dev-guide.rust-lang.org/borrow_check.html));
  Perceus derives retain/drop placement from liveness (mirrored in
  `papers/`, via `docs/ownership.md`).
- **Evidence you can hold but not forge** — the "parse, don't validate"
  discipline: represent the *proof* of a check as a value only the
  checker can construct
  ([Alexis King, 2019](https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/)).
  In-repo precedent: ADR 0055's `Blame`.
- **Crate boundaries as standing architecture enforcement** — in-repo
  precedent: `talk-mir` (ADR 0047) has three consumers and zero seam
  violations since extraction, because violations do not build.
