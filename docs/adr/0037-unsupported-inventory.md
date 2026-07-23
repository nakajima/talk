# ADR 0037 — `BackendError::unsupported` inventory

Companion to `0037-eliminate-backend-unsupported-behavior.md` (step 0). Every one
of the 65 sites is listed with its trigger, disposition, and support path.
Dispositions use the ADR's vocabulary:

- **VALID** — behavior gets implemented; the site disappears into a mechanism.
- **DUP** — duplicate guard for a gap owned by another site; closes with it.
- **FRONTEND** — semantically invalid source; the frontend/MIR analysis gains a
  structured diagnostic and the backend site becomes an invariant.
- **LINKER** — missing external supplier; becomes a missing-supplier diagnostic.
- **ICE** — recovery-only form or violated invariant; becomes an internal
  compiler error (requires a test proving frontend erasure/rejection first, per
  the admission rule).

All bare `:line` references are `src/backend/mir/mod.rs`.

## Summary

The 65 sites collapse into **seven implementation mechanisms**, **~7 frontend
diagnostics**, **2 linker diagnostics**, and **~12 ICE demotions**. The
mechanisms, in ADR dependency order:

| # | Mechanism (ADR §) | Sites closed |
|---|---|---|
| A | Generic evidence threading (§2) | 3482, 4882, 4896, 5135, 6691, 6706, 6720, 8024, 8387, 8398, 8728, glue:419, glue:479 (13) |
| B | Derived show/equality over all shapes (§2) | glue:142, glue:243, 4532, 4554 (4) |
| C | Owning closure environments (§3) | 2728, 5265, 5332, 5346, 5472, 5523, 5957, plus the `Ty::Func` half of 500/5000 (7+) |
| D | Place model + initialization (§1) | 5411, entries:353, 5984, 7867, 8044, half of 6631 (6) |
| E | Pattern ownership + dynamic projection (§4) | 5636, 7018, 7037, 7142, 6130, float arm of 7467 (6) |
| F | Globals + external supply (§5) | 5937, 6405, 6412, entries:270 (+ LINKER 2058) (5) |
| G | Ambient core effects as fallback handler (§6) | 8546 (1) |
| H | Inline IR completion (§7) | 5086, 9495 (2; 9383/9433/9457 go FRONTEND, 9411 goes ICE) |

Three open questions need a decision before their sites can be dispositioned
finally (see "Open questions" at the end): value-carrying `continue` (5886),
struct destructuring patterns (5652/7467), and positional protocol members
(7843/8001).

---

## A. Generic evidence threading (§2) — 13 sites, one mechanism

> **STATUS 2026-07-22: population fixed for every fixture-reachable shape.**
> Three roots closed: (1) the backend's `rigid_constraints` re-derived
> constraint facts by scanning effect signatures only — it now reads the
> frontend-published `TypeCatalog::param_bounds` (typing publishes,
> lowering reads) expanded through `protocol_and_supers`, which fixed
> plain function constraints, where-clauses, refined protocols, struct/
> enum owner params, and protocol-default `Self` in rigid check-all mode;
> (2) handler-clause frames now inherit the enclosing frame's witnesses
> and dictionaries through their environments like ordinary closures;
> (3) frame witness maps normalize rigid keys to one canonical spelling
> (`canon_rigid`) at every insert and lookup — bind sites keyed raw or
> imported spellings inconsistently. `method_owner_params` also covers
> inherent extend members now. Two KNOWN_STRICTER reference programs
> promoted to enforced pins
> (`heap_rvalue_arg_through_witness_call_releases`,
> `protocol_default_method_receiver_is_borrowed_param`).
> The `unsupported` branches remain as population guards; residual
> unprobed shapes before ICE demotion: glue:419 (compound rigid payload
> in a requirement closure — needs a conditional-conformance fixture,
> e.g. `Array<T>: Showable` packed into an existential) and :6691
> (a generic effect instantiation unresolved by instantiation records or
> structural solving — no reaching fixture found yet).

**Current machinery.** Rigid generics carry evidence as
`param_witnesses: Symbol → (drop, retain)` and
`param_requirements: (Symbol, protocol) → Vec<LocalId>`, bound by
`bind_witness_params` (:4851), forwarded by `push_witness_block` /
`append_witness_args` (:4875–4938), inherited into closures by `capture_env`
(:8712) / `bind_env` (:1042). Every site below is a lookup miss in one of these
maps — the success path already exists at each site.

**Fix.** Make evidence population *total*: every rigid param reachable in a
frame has its witness pair and per-constraint dictionaries bound, across direct
calls, indirect calls, closure envs, existential packs, effect-clause frames
(the re-perform path), and glue. Once population is total, every lookup becomes
infallible and the branches demote to ICE guards.

| Site | Miss | Notes |
|---|---|---|
| :3482 | drop witness at implicit drop point (`drop_value` `Ty::Param` arm, :3469) | deferred error; success path :3473 |
| :5135 | retain witness (`retain_value` `Ty::Param` arm) | mirror of :3482 |
| :4882 / :4896 | witness / dictionary at call boundary (`push_witness_block`) | canonical pair |
| :6706 / :6720 | same, in effect-clause re-perform (:6697) | inherit evidence into clause frames |
| :8387 / :8398 | same, in `compile_existential_pack` (:8349) | inlined copy of the :4882/:4896 lookups |
| :8024 | dictionary at rigid-generic member dispatch (:7999) | |
| :8728 | dictionary in `capture_env` (closure env inherits rigids) | |
| glue:479 | witness in `glue_closure` (`glue_witness_params` miss) | |
| glue:419 | compound rigid payload: `witness_params(subst)` non-empty in `requirement_closure` | extend the `MakeClosure` at glue:456 to capture inner rigid witnesses, as `glue_closure` already does at glue:475–487; widen the requirement-closure arity contract |
| :6691 | generic effect instantiation unresolved by `expr.instantiation` or structural `solve_param` (:6683) | strengthen resolution to consult checker-published instantiation; ICE if frontend proves all effect generics pinned |

**Related ICE:** glue:406 (existential requirement with neither a conformance
witness nor a protocol default). If the frontend accepted `payload : P`, every
requirement resolves — a miss is a broken conformance-selection invariant.
Becomes an ICE carrying `payload_ty`/`protocol`/`name`. (Sibling non-unsupported
guard: `:8440`.)

## B. Derived show/equality (§2) — 4 sites

`emit_show` (glue:134) and `emit_equality` (:4480) synthesize checker-derived
`Showable`/`Equatable` bodies. The checker (`try_derive`,
src/types/solve/conformance.rs:377) only grants derivation when every
field/payload conforms, so the reachable gaps are:

- **glue:142 — VALID.** `emit_show` has no `Ty::Tuple`/`Ty::Record` arms.
  `emit_equality` already shows the shape at :4537–4553
  (`emit_field_equality` with `tuple_layout`); mirror it with `emit_sub_show`
  (:4442). Fixture: derived show of a struct with a tuple field.
- **:4554 — VALID.** `Ty::Param` leaf: `struct Box<T: Equatable>` compiled
  generically recurses equality into a rigid `T` field. Add a `Ty::Param` arm
  dispatching `equals` through the param's conformance dictionary
  (`param_requirements`) — parallel to `drop_value`'s witness dispatch. The
  same arm is needed in `emit_show`.
- **:4532, glue:243 — ICE.** Nominal leaf with neither conformance witness nor
  struct/enum def. `try_derive` makes this unreachable for well-typed derived
  conformances; demote after an erasure test.
- **Frontend guard:** structural conformance must never be published for shapes
  whose operation has no semantics (function equality/show) — enforced at
  publication, not in glue.

## C. Owning closure environments (§3) — the motivating family

**Current state.** Closures are Copy values with borrow-only captures:
`check_copy` treats `Ty::Func` as trivially copyable (:4953), `MakeClosure`
(:259) has **no teardown counterpart** — `drop_value` (:3378) and
`retain_value` (:5104) have no closure arm. Env layout is built/bound in one
pair: `capture_env` (:8712) / `bind_env` (:1042) — captured values, then
per-rigid witness pairs + dictionaries, then effect capabilities. The Copy
gates: `check_captures` (:5247, implicit captures) and `check_capture_list`
(:5302, explicit modes).

**Fix.** Environments become type-aware owning values: slots record capture
mode + value operations; generated env retain/drop glue (modeled on
`glue_closure`, glue:468) plugs into `retain_value`/`drop_value` via a new
closure arm; the last closure reference releases every owning capture exactly
once. Managed captures retain a snapshot per the implicit-sharing decision
(`docs/ownership-rethink-plan.md`).

| Site | Case | Disposition |
|---|---|---|
| :5265 | implicit capture of owned value (`check_captures`) — **the ADR's motivating `self` capture** | VALID |
| :5332 | `[consuming x]` of owned value (move-tracking already exists at :5342) | VALID |
| :5346 | `[borrow x]` of owned value | VALID; escaping stored borrows need frontend escape analysis or promotion to owning stored view |
| :5321 | `[copy x]` of non-copyable | **FRONTEND** — genuine language rule (ownership diagnostic), not a capability gap |
| :5523 | mutated+captured owning local (celled path, `bind_owned_pattern`) | VALID — cells become owning slots with drop glue (`CellNew/Get/Set`, :270) |
| :5957 | assignment to captured value not cell-promoted (`cell_scan`, :1032) | VALID — cell every captured-and-assigned binding (or mutable-borrow slot) |
| :2728 | *named* nested `func` with captures called by name (`compile_func`) | VALID — route `CallableBody::Func` with captures through the closure-value path |
| :5472 | generic local function that captures | VALID — env carries the witness bundle (A); needs per-instantiation strategy |
| :500 / :5000 (`Ty::Func` half) | `check_copy` value classification of function-typed values | VALID once closures have real value ops |

## D. Places and initialization (§1) — 6 sites

**Current state.** `PlaceChain` (:1265) = local/global base + named-field links
only. `resolve_place` (:4129) returns `None` for positional tuple elements,
generic/existential receivers, and rvalues. No uninitialized-storage state.

**Fix.** The ADR §1 place representation: roots local/global/capture/temporary;
links add tuple-element and evidence-based generic projection; operations
include `initialize` with definite-assignment dataflow and temporary
materialization for `mut` rvalues.

| Site | Case | Disposition |
|---|---|---|
| :5411 + entries:353 | `let` without initializer (local + named-entry global; entries derives ty from `rhs.ty` — must come from the annotation) | VALID; read-before-init becomes a dataflow diagnostic |
| :5984 | assignment through unresolvable place (`t.0 = v`, generic receiver field) | VALID — tuple-element `PlaceLink`, evidence projection |
| :7867 / :8044 | `mut` protocol requirement on an rvalue existential/generic receiver | VALID — materialize a temporary place, reuse the existing writeback paths (:7906 Repack, :8050 Place) |
| :4643 | `mut` call argument that is a true rvalue | **FRONTEND** — verified gap: the checker validates place-ness for assignment targets (`infer_assignment_target`, stmt.rs:357) but not for `mut` args; add the mirror check, then :4643 is an ICE guard |
| :6631 | `mut` effect argument, `resolve_place` `None` | split: real-but-unspineable places (tuple element) → VALID with :5984; true rvalues → FRONTEND with :4643 |
| :5994 | assignment-target catch-all (frontend already rejects via `InvalidAssignmentTarget`) | ICE |
| :5937 | assignment to a global with no allocated slot | VALID — belongs to family F (stable slots) |

## E. Patterns and dynamic projection (§4) — 6+ sites

**Current machinery.** `record_cells` (:7126) is the single record label→slot
authority; `settle_owned_match` (:6921) + `pattern_leaves_owned_unbound`
(:7086) implement per-payload ownership accounting; `bind_owned_pattern`
(:5509) is the `let`-position twin.

| Site | Case | Disposition |
|---|---|---|
| :5636 + :7037 | pattern binds a field *and* its interior on an owned value (`let` + match twins) | VALID — one rule in both compilers: interior is borrowed from the whole / retained snapshot; two binders never claim one reference |
| :7018 | or-pattern alternatives leave different owned payloads unbound | VALID — settle per-alternative on each alternative's matched edge (each already has its own test block, :7387; tag known via `match_tag_cache`) instead of settling `alternatives.first()` |
| :7142 | record pattern on an open row (`row.tail.is_some()`) | VALID — runtime row-layout dictionary threaded as evidence (mechanism A); `record_cells` emits dynamic slot lookups. Real semantic work, flagged in ADR consequences |
| :6130 | field read (`Proj`) on rigid/existential receiver | VALID — layout/witness projection, same machinery as the member-dispatch paths at :7848/:8007 |
| :7467 | pattern-test catch-all | split: `LiteralFloat` **VALID** (trivial — mirror the `LiteralInt` arm with `ScalarOp::FloatCmp`); `Struct` unreachable (frontend rejects, pattern.rs:542); `Bind(non-Resolved)` **ICE** |
| :7491/:7501/:7510 | string-pattern scrutinee not nominal / missing `byte_count`/`storage` | **ICE ×3** — frontend pins string patterns to `String`/`Character` (pattern.rs:380/389); these guard Core layout invariants |
| :7843 / :8001 | positional member on existential / generic value | ICE pending reachability test — protocol requirements are named-only, so no frontend form emits this today; if one appears, implement via layout/witness evidence per §4 |

## F. Globals and external supply (§5) — 5 sites

**Current state.** Two-tier globals: `globals: Symbol → initializer` for every
top-level `let` (:1816), but `global_slots` allocated only on the entry-init
path (entries:325). Demand-compiled readers only inline scalar literals
(:6392).

| Site | Case | Disposition |
|---|---|---|
| :6405 | global with non-literal initializer read from a function | VALID — every global gets a stable slot + initializer thunk + init state, demand-independent; readers use the existing slot branch (:6240) |
| :5937 | *write* to a global with no slot | VALID — same slot fix |
| :6412 | variable resolves to no local/slot/static/callable/global | split: declared-but-unsupplied callable → **LINKER**; unresolved recovery → **ICE** |
| :2058 | call to a name with no compilable body (`demand`) | **LINKER** — name resolved, body absent; structured missing-supplier diagnostic. (Core primitives carry `@_ir` bodies and are unaffected.) |
| entries:270 | linear global teardown | VALID — requires the §5 whole-program finite-exit analysis (callable summaries → fixed point); invalid programs get the ordinary linearity diagnostic. Genuinely new machinery, unique site |

## G. Ambient core effects (§6) — 1 site

**:8546 — VALID.** `install_handler` rejects any handler over a
`ModuleId::Core` effect. Core performs currently bypass the handler stack
entirely: `is_io_effect` short-circuit at :6593 lowers straight to `Inst::Io`
via `compile_io_perform` (:8466), and `closure_effects` filters Core at :8701 —
the reject exists because a user handler would be silently skipped.

Fix per §6: the runtime host becomes the *outermost fallback handler*. Route
typed core performs through the normal `FindHandler`/`Inst::Perform` path with a
bottom-of-stack host clause; remove the exclusions at :8545/:8701 and the :6593
bypass. Allocator/raw-memory primitives stay unhandleable intrinsics (split any
effect that conflates the two first). Coupled to mechanism A on the
perform-lowering path.

## H. Inline IR (§7) — 6 sites

The instruction enum (26 variants) is fully covered by the two lowering
matches; the operand enum is not.

| Site | Case | Disposition |
|---|---|---|
| :9411 | instruction catch-all | **ICE** — union of the two matches covers all 26 variants; replace with exhaustive match |
| :9495 | operand catch-all | VALID — `Uninit`, `Poison`, `Record`, `RawPtr`, `RawBuffer` fall through and §7 requires all of them; `uninit`/`poison` get validated trap semantics and must not escape as source values |
| :5086 | type annotation not resolved-nominal/borrow (`annotation_value_ty`, :5066) | VALID — resolve the same `Ty` shapes ordinary source uses; invalid combos → FRONTEND |
| :9383 / :9433 / :9457 | cmp/arith/bitwise on an inadmissible type | **FRONTEND** — invalid operation/type combination; add inline-IR op/type validation to the frontend, arms become exhaustive. Any intentionally-valid extension (e.g. Byte arithmetic) extends the op tables instead |

## I. Exhaustive fallbacks (§8) — remaining catch-alls

| Site | Fall-through set | Disposition |
|---|---|---|
| :5501 | `DeclKind` other than `Let`/`Func` in a body | **ICE** after an erasure test |
| :6775 | expr catch-all | split: `RecordLiteral` (spread/out-of-order rows, build.rs:317) **VALID** — evaluate source-order, permute to row layout; `Constructor`/`Member` used as *values* (not called) **VALID** — captureless `MakeClosure` mirroring :6373; `Variable(Unresolved)` and `Temp` **ICE** |
| :5652 | `bind_owned_pattern` catch-all | `Struct` destructuring is frontend-rejected today (pattern.rs:542) → unreachable, see open questions; refutable literals/`Or`/`Variant` in `let` position and `Bind(Unresolved)` → **ICE** |
| :8846 / :8853 | construction of non-nominal / no-struct-def type | `T()` through a protocol init requirement on a still-rigid `T` **VALID** (extend the existing `ViaRequirement` handling at :8871–8917 with mechanism A); enum-via-`Constructor` if the frontend emits it **VALID**; residual **ICE** |
| :500 / :5000 | `check_copy` value classification | `Ty::Func`/`Ty::Param`/open-row arms become real (mechanisms C, A, E); residual nominal-without-def **ICE** |
| :5886 | `continue <expr>` in an ordinary loop (handler-clause resume is handled above it) | **RESOLVED 2026-07-22** — effect resume respelled `'continue` (`StmtKind::Resume`); loop `continue` takes no value (parse error); the unsupported site is deleted and resume works at any loop depth |

## Open questions (need a language decision)

1. ~~**`continue` with a value in a loop (:5886).**~~ RESOLVED 2026-07-22: the
   effect resume is now spelled `'continue` (its own `StmtKind::Resume`), loop
   `continue` takes no value, bare `'continue` type-checks unit against the
   effect's return type, and resume works from any loop depth inside a clause.
2. ~~**Struct destructuring patterns (:5652, :7467-Struct).**~~ RESOLVED
   2026-07-22: implemented end-to-end. Parser produces
   `Point { x, y: pat, .. }` (shorthand + rest); resolver declares binders and
   resolves the struct name; checker validates fields against `StructInfo`
   (unknown/duplicate/missing diagnostics) with generic instantiation;
   exhaustiveness models structs as single-constructor products
   (`Ctor::Struct`); backend lowers `let` and `match` positions via
   `struct_cells` (GetField for value structs, ObjectGet for heap structs —
   heap fields settle as views borrowed from the object, which drops once).
   The `Struct` variants leave the :5652/:7467 catch-alls' fall-through sets.
3. **Positional members on existentials/generics (:7843, :8001).** Protocol
   requirements are named-only, so these look unreachable. The admission rule
   requires a reachability test before demoting to ICE.

## Suggested wave order (matches ADR §Implementation order)

1. **D — places/initialization** (unblocks assignment, `mut` writeback, uninit
   `let`; includes the :4643 frontend diagnostic).
2. **A — evidence threading** (13 sites; other families consume it).
3. **B — derived show/equality** (small, sits on A).
4. **C — owning closure environments** (motivating case; sits on A + B glue).
5. **E — patterns** (sits on A for open rows/projection, C conventions for
   ownership accounting).
6. **F — globals + linker diagnostics** (slots first, then linear-global
   analysis, then the LINKER conversions).
7. **G — ambient core effects** (waits for closure/evidence layout to settle).
8. **H — inline IR** (reuses places + value ops).
9. **I — fallback removal + ICE demotions** (each demotion paired with its
   erasure/rejection test).

Quick independent wins (no mechanism dependency): the `LiteralFloat` pattern
arm (:7467), the :9411 exhaustive match, and the three string-pattern ICE
demotions once their frontend-shape tests exist.
