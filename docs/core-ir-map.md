# Core IR migration map (Track C, phase 3)

Status: in progress (2026-07-03)

> **Effects note (2026-07-03, post-C5):** ADR 0011 replaced the M7 abort
> machinery this map's older entries mention. There is no abort-capable
> calling convention, no `try_mir_effect_split`, no `HandlerCap` /
> `handler_caps`, and no statement-spine restriction anymore: functions
> take capability parameters for the user effects in their rows, the
> `@handle` capability captures its scope's return continuation as the
> delimiter (VM: one-shot `MakeCont`/`CallCont`), `continue v` is the
> capability returning, and a perform's own continuation is the
> resumption — valid in any expression position. Handler bodies still
> lower from scaffold blocks exactly as described below.

Strategy: **HIR becomes Core in place.** There is no parallel tree and no
big-bang `build_core` — each step removes or splits one HIR form via
type-directed elaboration in `hir/build.rs`, then deletes the dead arms in
flow (`moves`/`liveness`/`loans`/`cfg`), the MIR builder, and lowering.
Every step lands green (eval≡VM suite + `run_heap_eval` balance tests) —
the strangler pattern C1/C2 already used. This aligns with the
annotated-tree rule: one tree, annotated stage by stage, never bridged by
side maps.

## Expression forms (19 at start of C3)

| HIR form | Core disposition | How |
| --- | --- | --- |
| `LiteralInt/Float/True/False/String` | one `Lit(Literal)` atom | mechanical merge (C3a) |
| `As` | erased | build grafts the inner expr, overlaying the As node's id/span/ty/pack/auto-clone; the ascription's work is finished in the checker; packs already ride `existential_pack`, not the form (C3b) |
| `RowVariable` | erased or diagnosed | typing-only artifact; verify unreachable below typing, then delete (C3c) |
| `Variable`, `Constructor` | atoms | already atomic; keep |
| `Tuple` | `Con` (positional record) | unify with `RecordLiteral` — both lower to λ_G tuples in canonical field order (C3d, needs pattern-side unification too) |
| `RecordLiteral` | `Con` | with `Tuple`; spread is a checked-then-elaborated copy |
| `LiteralArray` | keep (runtime container ctor) | collapses only when container ctors become ordinary calls |
| `Call` | `App` | variant-construction split-off (`Con`) is type-directed at build; trailing blocks become ordinary lam args with C4 |
| `CallEffect` | `Perform` | rename/keep; already perform-shaped |
| `Member` | split: `Proj` (field) vs dispatch | type-directed via baked `member_resolution`; the 33-site monster (C3e) |
| `Func` | `Lam` | keep |
| `Match` | `Case` | keep (the pattern-matrix compile stays in lowering per Maranget) |
| `Block` | dies with C4 | statement control flow → join points |
| `InlineIR` | `Prim` | keep (unsafe escape hatch) |

## Statement forms (8) — C4 territory

`Expr, If, Return, Break, Assignment, Loop, Continue, Handling` collapse
to `let` + `letrec` join points at build time (Maurer et al., PLDI 2017);
until C4 they stay. MIR's builder then shrinks with them (C5: statements
carry Core operands).

## Order and status

- C3a literals → `Lit` — DONE (2026-07-03)
- C3b `As` erasure — DONE; `as` expressions now actually run (previously
  hit lowering's unsupported catch-all); `graft` in `hir/build.rs` is the
  reusable erase-a-wrapper helper (id/span/ty/pack/auto-clone overlay)
- C3c `RowVariable` — DONE; had NO construction site anywhere — deleted
  from surface AND HIR (parser never emitted it)
- C3c′ 1-tuples (parenthesization) erased at build via `graft`; lowering's
  two 1-tuple special cases deleted
- HIR expression forms: 20 (branch start) → 12
- C3d `Tuple`+`RecordLiteral` → `Con` — DEFERRED: a canonical-order `Con`
  at build would reorder record-field evaluation (observable via effects);
  the honest version needs the C5 operand story. Record-order baking is
  the only cheap piece and saves little.
- C3e `Member` split — DONE: `Proj(receiver, label, field)` for stored
  fields, classified once at build by `stored_field_symbol` (now used
  NOWHERE else); `Member` keeps methods, leading-dot variants, and
  anonymous-record fields (no catalog symbol). `place_for_expr` and the
  MIR builder's key paths / embed walks / assignment roots are structural;
  `place_for_expr` and the whole `mir_annotate` chain lost their
  `TypeOutput` parameter. `is_field_value_callee` = a `Proj` pattern match
  (plus the record-by-label fallback).
- C3f variant construction → `Con` — DONE: `Con { enum_symbol, tag,
  variant_symbol, args }` classified at build (`variant_resolution` mirrors
  the old `variant_target`: Direct resolution at the callee or call node
  against the merged catalog — `TypeOutput.catalog` includes imports, so
  cross-module enums classify fine). The constructor instantiation (GADT
  evidence) overlays from the resolution node. Payload-carrying variants
  used bare stay `Member` (function values). To flow, `Con` is an
  aggregate: payloads consume like tuple elements, provenance unions
  borrow-carrying payloads; no more `Statement::Call` for constructions —
  consumption rides the consuming statement. Lowering's `variant_of` /
  `variant_target` / `try_variant_value` deleted; the perform-request
  matcher is one `Con` arm. `Member` now covers only: method callees,
  anonymous-record fields, bare payload-carrying variants.
## Status: C4 DONE, C5 substance DONE (matches + calls) — 2026-07-03

**Calls landed after matches, same recipe:** `Statement::Call` carries
`{expr, temp, result_ty}` and IS the evaluation point — lowering binds a
`call_temp` continuation (raw/unpacked: the node's pack and auto-clone
apply at the `Temp` read), abortable calls split the rest at their own
statement via `MirRestBinding::Temp` (the spine restriction is local
now), and flow records `call_provenance` into
`MoveState.temp_provenances` for the consuming statement's borrow
checks. Temp types are PRE-pack payloads; temps stay out of the
block-cache key (join dedup — reads are def-adjacent or bound by their
construct's single-lowered join closure). Embedded statement expressions
are now straight-line pure trees over atoms, places, and temps.

Remaining work is mechanical, best done post-landing: the Operand enum
swap (mass signature churn), Perform args, aggregates-as-Rvalues,
Tuple/Record→Con (C5c), and the C6 pass decomposition.

**The match flattening landed: matches lower with value-carrying joins.**
`hir::ExprKind::Temp(u32)` is the operand bridge; the builder mints a
temp per match, stores `(temp, result_ty)` on `Terminator::Switch`, and
substitutes `Temp` for the match node in every later statement AND
terminator embedding (`TempSubstituter` in `push_statement` /
`substitute_temps_expr` for scrutinees; handler/trailing/function payload
copies are exempt — they feed the standalone fallback). Lowering's Switch
arm builds `match_join = λt. <join walk with ctx.temps[t]>` (θ-substitute
the stored type per instantiation — generic method tails!) and runs
`compile_match` with the arm blocks; arm `ReturnValue{Continuation}`
tails apply it with the value, void tails deliver via `deliver_at`.
**The Switch join-skip and embedded-Match evaluation are dead** (probe:
zero hits suite-wide; the `lower_expr` Match arm survives as the
standalone-fallback guard). Flow parity was free: Match was already
opaque to `consume_expr`, and `Temp` is a free atom. `ctx.temps` rides
`Ctx` (and `MirCtxKey` for block-cache soundness).

Next flattening targets, same recipe: calls → temps (retires the
opaque-embedded-call double bookkeeping and `try_mir_effect_split`'s
spine restriction), then aggregates, then the mechanical Operand swap.

## Former status (C4/C5a)

C4a/b/c landed: handler bodies and trailing blocks are scaffold CFG
blocks under a shared `Terminator::Handler` (may-execute edges); the
capability closure lowers from the scaffold (`lower_handler_from_scaffold`,
zero fallback hits suite-wide); `continue v` retargets to the handler
join via the builder's `handler_stack`; **the whole tree walk is deleted**
(walk_block/walk_stmt/walk_match/schedule_drop/…, `Diverges`, `cfg_exprs`
— ~350 lines). Flow is pure CFG dataflow. Parity and balance pinned for
both constructs. Residuals: trailing-block LOWERING still tree-lowers the
embedded copy (balance pinned — switch to scaffold with C5b);
continue-with-value inside a trailing block inside a handler now targets
the outer handler's join (tree said unsupported; unexercised).

C5a landed for `Read`: `{node, ty, place, consumes, pack}` — the operand
prototype in production. The builder's `push_reads` emits one place-
carrying read for place-shaped chains, else boundary-only reads per chain
node (the old walk's descent, made explicit); the annotate pass writes
`consumes` as a statement field; `check_use`/`check_invalidated_use` are
node+ty based; `check_boundaries` is the operand-level boundary rule.

## C4–C6, decomposed for this branch (2026-07-03)

**Architectural finding that reshapes C4:** the CPS lowering already
functionalizes the CFG — `lower_mir_block` emits one λ_G function
(`mir_bb`) per reachable block and jumps are applications. Join points
exist; ADR 0010 built them. C4's remaining content is therefore NOT a new
representation — it is **retiring the last tree-walked statement surface**,
after which "statement control flow" is CFG-only end to end:

- C4a. `Statement::Handling` carries a whole `hir::Block` that flow
  tree-walks (`walk_block`, the `cfg_exprs` save/restore) and lowering
  lowers standalone. Scouted 2026-07-03 — NOT a stored body (a handler
  body checks against the state AT the Handling statement, and its
  effects merge back: exactly CFG-edge semantics), so it is scaffold
  blocks in the enclosing body, the expr-position-match pattern. One
  atomic surgery, four parts:
  1. Builder: a `handler_stack` frame; Handling lowers to scaffold blocks
     (handler entry + join, both edges from the current block = the
     may-execute clone+merge); handler-local scope/candidates as usual;
     handler block ARGS seed like arm binders; **`Continue(v)` inside a
     handler is a RESUME, not a loop edge** — it must emit
     `ContinueValue` + a jump to the handler JOIN, never to
     `loop_stack`'s continue target.
  2. Engine: delete the Handling walk_block transfer; the edges do the
     clone+merge; seed handler args at the handler-entry edge.
  3. Lowering: the capability closure's body lowers FROM the scaffold
     blocks (a `lower_handler_from_scaffold` beside
     `lower_arm_from_scaffold`) with `inner.ret_k` as the tail delivery
     and `resume_k` for ContinueValue — replacing `lower_block` on the
     embedded copy. CRITICAL COUPLING: today handler-local drops ride
     the `Block.drops` carriers that walk_block RECORDS; flow and
     lowering must switch together or handler locals leak.
  4. Only then does walk_block lose its main client (C4c deletes it
     after C4b does the same for trailing blocks).
- C4b. Trailing blocks (`Call.trailing_block`) — same treatment: stored
  bodies, engine-checked; the Call statement references the body.
- C4c. With a and b done, delete `walk_block`/`walk_block_nodes`/
  `cfg_exprs` and the `Block.drops`/`Stmt.drops` carrier fields — flow
  becomes a pure CFG dataflow with no tree mode. The `hir::StmtKind::If`
  divergence rules stay in the CHECKER (surface), which never collapses.

**C5 (the simplified MIR Pat asked for): flatten evaluation-carrying
statements to operands, kind by kind.** Ordered by embedded-expr role:

- C5a. Flow-only statements first — their exprs are never lowered:
  `Read{expr}` → `{node, place, ty}` (lowering already skips Read;
  the consumes-skip becomes a bool the annotate pass writes).
  `Perform{expr}` similarly (args become operand list).
  Scouted 2026-07-03, field-level: the builder pushes `Read` only for
  `Variable`/`Proj` (place-shaped) exprs, and the faithful payload is
  `{node, ty, place: Option<Place>, consumes: bool, pack:
  Option<ExistentialPack>}` — ty+pack feed `check_object_boundaries`,
  place feeds `check_use` (None for call-receiver chains, where today's
  walk is a no-op under cfg_exprs), consumes defaults false and is
  written by annotate (TopLevelErrors bodies error WITHOUT annotate —
  default-false is load-bearing). That five-field payload IS the
  `mir::Operand` prototype, and the Annotator must learn to write
  statement fields, not just drive embedded exprs — so C5a is the
  opening move of C5b, not a separate quickie.
- C5b. Define `mir::Operand` (place | constant | node-ref to a
  statement-produced temp) and `Rvalue` (con / proj / call / closure /
  literal-array / record). Migrate `Bind`/`Assign`/`ConsumeValue`/
  `ReturnValue`/`ContinueValue` one kind at a time: the builder flattens
  subexpressions into temp-producing statements (three-address form),
  and lowering's expression-tree walkers (`lower_expr`, `try_pure`,
  `lower_args`, `embed_acquires_then`) shrink to operand lookups.
  This retires the ADR 0010 departure ("no three-address flattening"),
  the embedded-copy duality, and the scaffold machinery: expression-
  position match arms become ordinary blocks because VALUES flow through
  temps, not through embedded trees.

  **Opening surgery, spec'd 2026-07-03 (do this first, fresh window):
  Switch lowering with value-carrying joins.** The bridge is
  `hir::ExprKind::Temp(TempId)` — an atom the builder substitutes into a
  consuming statement's embedded expr where a flattened construct stood.
  For a match consumed by statement S: the builder terminates into the
  Switch (real arms, not scaffolding), arm tails stay
  `ReturnValue{Continuation}`, the join block holds S with the Match node
  replaced by `Temp(t)` (ty = the match's ty). Lowering's Switch arm
  DROPS the join-skip: lower the scrutinee, run `compile_match` with the
  arm blocks (this plumbing exists — `lower_arm_from_scaffold`), with
  `k = join closure λt. <join walk with t bound in env for Temp
  resolution>` (the `rest_mir_closure`/"after_perform" pattern). Flow:
  `Temp` is a non-place atom, no transfer effects (its consumption
  happened at the arm ReturnValue; `let x = match…` parity holds because
  consume_expr on Match is already opaque). What dies: the
  Switch join-skip, `match_scaffold_arms`, `deliver_at` for matches, and
  the enclosing-statement embedded-Match evaluation. Statement-position
  matches ride the same path (their S is `ConsumeValue{Temp}` — a
  discard). Then Calls → temps (retires opaque-embedded-call double
  bookkeeping), then aggregates, then the Operand enum replaces the
  Temp-in-hir bridge mechanically.
- C5c. `Tuple`+`RecordLiteral`→`Con` finishes here (deferred C3d): as
  Rvalues, field reordering is a temp permutation, so record-field
  evaluation order is preserved by construction.

**C6: decompose `lower/` into ordered narrow passes** — match-compile
(Maranget stays), monomorph/demand, closure-conv, CPS emission — each
consuming the operand MIR. `Member`'s method-dispatch role and
`is_field_value_callee` land in the dispatch pass. Only start after C5b:
the passes' interfaces ARE the operand language.

Sizing honestly: C4a/C4b/C5a are checkpoint-sized. C5b is the long arc
(it rewrites the builder and the lowering entry paths — several sessions,
one statement kind per checkpoint). C6 follows C5 mechanically.

Each step's gate: full suite + a balance test for the construct touched
(see docs/confidence-and-core-plan.md, Ordering).
