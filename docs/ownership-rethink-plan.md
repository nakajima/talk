# Ownership rethink: implicit sharing, one dataflow layer

Status: language decision approved 2026-07-18. Design ready for
implementation; waves and exit criteria below.

## Why a rethink and not patches

An external review of this branch found that the ownership checker
accepts or miscompiles programs the reference rejected: a compiled
double free (`tuple_match_keeps_owned_and_borrowed_payload_drops_separate`),
a runtime invalid-pointer trap
(`rejects_function_assigning_a_globally_borrowed_global`), and five
silent acceptances of programs the corpus pins as errors. All were
hiding in the flow gate's `KNOWN_FAILING` opt-out list.

The causes are structural, not local:

1. **There is no borrow ledger.** The checker's whole flow state is a
   set of moved locals (`mir/mod.rs`, `moved: FxHashSet<LocalId>`).
   Borrows exist only as type classification used for drop decisions.
   No rule that needs "who currently borrows `s`" can fire, because
   the fact is never recorded.
2. **Flow sensitivity is hand-threaded per AST construct.** Each
   control-flow construct hand-merges move state (the match-arm union
   logic); loops, handler bodies, and trailing blocks each need their
   own copy of that care or silently go without. The loop-carried
   borrow case slipped through because an AST walk visits a loop body
   once, so facts from the bottom of the loop never reach its top.
   Every future construct is a fresh chance to forget a merge.
3. **Drop emission reads that same hand-threaded state**, so the
   double free is cause 2 expressed as codegen: match payload
   ownership decided by pattern shape, not by scrutinee provenance.

This failure mode is not new to this branch. The previous system's
five-track review (`docs/ownership-soundness-plan.md`) confirmed six
memory-safety holes in the *frontend* flow pass and named the same
systemic cause: invariants held by a trust chain with no verifier
behind it. Two independent implementations grew the same class of
holes because both hand-maintain flow state instead of computing it.
Rust's borrow checker went through exactly this history: the AST-era
checker accumulated soundness bugs and ergonomic rejections until
non-lexical lifetimes (RFC 2094) moved the analysis onto MIR as a
dataflow fixpoint. We have the same move available and the same
reasons to make it.

## The language decision (approved)

Talk is a value-semantics language over reference-counted,
copy-on-write aggregates. In that world a borrow is representationally
a non-owning reference to a refcounted box, a clone of an aggregate is
a retain (O(1)), and mutation already goes through `IsUnique`/CoW.
The decision: **make sharing implicit and let the compiler infer
retains and releases; ownership becomes an optimization the compiler
discovers, not an obligation the programmer proves.** This is the
Perceus model (Reinking, Xie, de Moura & Leijen, "Perceus: Garbage
Free Reference Counting with Reuse," PLDI 2021) as shipped in Koka,
and "Counting Immutable Beans" (Ullrich & de Moura, 2019) as shipped
in Lean 4; the CoW half is Swift's value-semantics contract.

Semantic rules:

1. **Use never fails for shareable types.** A non-last use of a value
   retains; the last use moves. Last-use placement is liveness, and
   liveness is computed, not threaded (Perceus §3; the drop machinery
   from wave 9 — deinit index, shared drop glue — remains the emission
   substrate).
2. **Escape converts borrowed to owned by retaining.** Returning,
   storing to a global, or capturing a value that holds a borrow
   retains the referent instead of erroring. Later mutation of the
   original owner hits the existing CoW machinery, so the escaped
   value has snapshot semantics — the same observable behavior value
   semantics gives everywhere else.
3. **`consume` is a callee-side ownership contract, not a caller-side
   proof burden.** The callee receives ownership; if the caller uses
   the value afterward, the compiler retains before the call. (The
   reference already did this for generics —
   `generic_early_consume_auto_clones_without_marker` pins it; the
   rule becomes uniform.) Consuming an *unclonable* value twice stays
   an error.
4. **What remains a static error** — exactly four categories:
   - **Exclusivity.** Any access to a place while a `&mut` loan of it
     is live, from outside that loan (Swift SE-0176, McCall, "Enforcing
     Exclusive Access to Memory", narrowed: adjudication showed the
     conflict must involve a live `&mut` *loan* — a long-lived alias
     whose in-place-write contract aliasing would silently break.
     Shared loans never conflict with anything, and transient exclusive
     accesses such as a `mut` method call don't conflict with live
     shared loans: CoW gives the shared reader a snapshot and the
     write lands in the owner). You cannot retain your way out of
     aliased mutation. This covers the loop-carried case.
   - **Linear values.** Types marked linear must be consumed exactly
     once on every finite path and never implicitly dropped or
     duplicated (`is_linear` in `mir/mod.rs`; Wadler, "Linear types
     can change the world!", 1990). Raw pointers and unique resources
     live here.
   - **Declaration wellformedness.** Borrow-typed fields only in
     `Borrowed`-marked structs, `mut`-marker parameter rules, and the
     other type-shape checks — unchanged.
   - **The unsafe gate.** `_alloc` and friends require the intrinsic
     `'unsafe` effect outside core. A lexical `@unsafe { ... }` block
     discharges that effect without installing a runtime handler.

The reject pins this retires are a deliberate language change: those
programs stop being errors and start being valid programs with
sharing. Wave A rewrites their expected outputs on purpose, case by
case, never by bulk edit.

## The analysis layer: one dataflow pass over MIR

All flow reasoning moves off the AST walk and onto built MIR, where
control flow — loops, match joins, handler re-entry — is just edges.
The infrastructure exists: MIR has a real CFG, and regalloc already
computes bitset liveness over it.

Components, each replacing hand-threaded state:

- **Places.** Locals, their field projections, and globals, arranged
  in a move-path tree (Rust's `MovePath`; formalized place-based
  reasoning in Oxide — Weiss, Matsakis & Ahmed, 2019).
- **Initialization fixpoint.** Maybe-initialized / definitely-
  initialized per place per program point, as forward dataflow
  (Kildall 1973; Rust's `MaybeInitializedPlaces`). Replaces the
  `moved` sets and every per-construct union.
- **Retain/release placement.** Liveness-driven: retain at non-last
  uses, move at last use, release at the last point a place is
  maybe-initialized (Perceus insertion, on the CFG rather than the
  AST).
- **Drop elaboration.** Scope-exit and unwind drops derived from the
  initialization fixpoint, not from builder bookkeeping (Rust MIR
  drop elaboration). The wave-9 cleanup chains consume the elaborated
  drops; the hand-maintained per-arm drop decisions are deleted. This
  kills the double-free class, not the one double free.
- **Loans and exclusivity.** A borrow instruction creates a loan; its
  region is its live range (NLL, RFC 2094 — Polonius is a possible
  later refinement, not a dependency). Error when a loan's region
  overlaps a conflicting access, per SE-0176's law: conflict requires
  at least one write. Back edges need no special handling — that is
  the point.
- **CFG fidelity for effects.** Handler bodies and trailing closures
  get honest zero-or-more re-entry edges (the old system's S5 hole
  was exactly a zero-or-one model). Perceus was designed for a
  language with effect handlers (Koka), so the insertion rules
  compose.

The AST-walk ownership machinery — `moved`/`moved_globals`, the arm
state unions, `continues_moved`, the match ownership special cases —
is deleted once the dataflow layer lands. The rethink should be a
negative diff in `mir/mod.rs`.

`talk check` runs the same analysis (build MIR, analyze, skip
lowering), which also closes the review's finding that `talk check`,
the LSP, and editor embeddings report no ownership errors at all.

## Corpus adjudication

The thirteen `KNOWN_FAILING` cases and the two runtime miscompiles,
under the new semantics:

| Case | Outcome | Killed by |
| --- | --- | --- |
| tuple_match_keeps_owned_and_borrowed_payload_drops_separate | runs, prints 32 | drop elaboration |
| rejects_function_assigning_a_globally_borrowed_global | accepted: global store retains; reassignment CoWs | escape rule + CoW |
| borrowed_marker_struct_cannot_escape_its_loan | accepted: return retains the loan's referent | escape rule |
| loop_carried_mutable_borrow_lives_until_storage_dead | still an error (exclusivity) | loan liveness |
| rejects_whole_struct_use_after_owned_field_move | accepted: field read retains, struct stays initialized | retain placement |
| rejects_borrowed_global | accepted: stored view retains its String | escape rule |
| rejects_raw_pointer_usage_in_safe_source | still an error | unsafe gate |
| allows_raw_pointer_usage_in_unsafe_source | runs; the exit leak fence stays authoritative for unsafe sources too (the pin program frees its allocation — manual memory must balance by exit, the programmer controls when) | unsafe gate |
| generic_early_consume_auto_clones_without_marker | accepted (rule 3) | retain placement |
| move_inside_handler_body_is_may_moved_after | accepted: non-last use retains across re-entry | CFG fidelity + retain placement |
| move_inside_trailing_block_is_may_moved_after | accepted, same | CFG fidelity + retain placement |
| heap_rvalue_arg_through_witness_call_releases | unchanged: fail-closed dictionary boundary, separate feature | — |
| protocol_default_method_receiver_is_borrowed_param | unchanged, same | — |

The remaining error pins in `tests/reference/flow/expected/` (73
`.error` files) are adjudicated one by one in wave A against the four
surviving error categories. Expected outcomes by family: exclusivity
and linear pins survive; "moves owned value" / "use after move" pins
on shareable types become accepts with retains; escape pins
(`rejects_returning_*substring*`, borrow-in-container escapes) become
accepts with snapshot semantics; wellformedness pins survive
unchanged. Every reclassification is recorded in the adjudication
table appended to this document, with the pin diff in the same
commit.

## Gate restructure

`KNOWN_FAILING` — one list that can hide a double free next to a
missing nicety — is replaced in `assert_flow_corpus`:

- Expected-reject cases have **no silent opt-out**. Every one must
  exit nonzero with its fragment. A `WRONG_REASON` list may relax only
  the message fragment, never the rejection itself. A reject whose
  enforcing wave has not landed sits in `PENDING_REJECTION`, which
  *asserts it does not reject yet* — the moment enforcement lands the
  assertion fires and the case must be promoted, so the list cannot go
  stale or hide a regression.
- Expected-accept cases may be parked in `KNOWN_STRICTER`, which
  asserts nonzero exit (we reject or trap where the reference ran —
  fail-closed, safe) and self-cleans the same way.

Under this rule the Tier 1/2 cases become ordinary failing tests the
moment the gate lands, which is the TDD entry point for every wave
below.

## Waves

- **A. Gate + adjudication.** Restructure the flow gate; adjudicate
  all 73 error pins against the four categories; rewrite retired pins
  (with the new expected stdout where the program now runs); restore
  the unsafe gate (small, independent, closes a security boundary
  immediately). Exit: gate compiles with must-reject unskippable; the
  soundness cases are visible failing tests; unsafe-gate pins green.
  **Landed 2026-07-18**: 51 pins retired, 22 survive (table below);
  the unsafe gate lives in `src/backend/mir/unsafe_gate.rs` and both
  gate pins are enforced; parked divergences are typed and
  self-cleaning (`KNOWN_STRICTER` 52 entries, `PENDING_REJECTION` 1).
- **B. Places + initialization fixpoint.** Move-path tree, bitset
  maybe-init/definitely-init over the MIR CFG. Runs beside the old
  state first, asserting agreement on the accept corpus (an internal
  check, deleted at the end of wave C). Exit: fixpoint results match
  hand-threaded state everywhere the old system is trusted; divergences
  are triaged as old-system bugs or new-system bugs, each with a test.
  **Landed 2026-07-18** as the balance verifier
  (`src/backend/mir/verify.rs`): the builder logs every Def/Use/Move/
  Drop decision and a forward fixpoint replays the log over the built
  CFG — the exactly-once checker ADR 0017 stage 2 promised. Places are
  locals + globals; field granularity was retired by the semantics
  (partial moves no longer exist). Debug builds verify every function
  that compiles clean; unwind edges carry state into cleanup chains, so
  chain reuse is checked too. Triaged divergences: two log-side fixes
  (post-return flushes discard like `push` does; Absent/Dead join to
  Dead — both mean nothing owned), and **one real leak** — sibling
  match arms share `owned_tys`, so an arm consuming a payload temp
  deleted the type a sibling's break-path flush needed, leaking the
  payload at runtime (confirmed against the counted allocator; the
  parser corpus hits the shape in `consume_or_recover_closer` and
  `parameters`). Fixed by making `owned_tys` a monotone type table —
  per-path truth lives only in `stmt_temps`/`moved` — with the repro
  pinned as
  `run_drops_a_payload_binding_on_the_break_path_after_a_sibling_arm_consumed_it`.
- **C. Retain placement + drop elaboration.** Liveness-driven
  retain/move/release; drops derived from the fixpoint; delete the
  AST-threaded sets, arm unions, and per-construct drop bookkeeping.
  Exit: the double-free case runs and prints 32; unwind/cleanup tests
  green; `bench/drops.tlk` instruction counts flat or better; net
  negative diff in `mir/mod.rs`.
  **Landed 2026-07-18** (rules 1–3 live; the deletion ledger continues
  as waves D–E retire the loan/escape error surface). A consume that
  is not the value's last use now retains instead of erroring —
  last-use comes from the frame's use counts, with an outer binding
  consumed inside a loop always sharing, and linear values, `*T`
  uniques, and witness-less generic frames keeping move semantics.
  Constructions consume with the destination slot's declared type
  (owned slot + borrowed source = donation; borrow-typed slot = view,
  so iterator Optionals pack as before), and a bind of owned payload
  reached through a borrow-typed layer retains its share — together
  these killed the tuple-match double free, whose pin now enforces
  "runs, prints 32". Twenty-one parked corpus cases promoted to
  enforced accepts; the bench pins never moved (last-use consumes
  still compile to plain moves).
- **D. Loans + exclusivity.** Loan creation, live ranges, conflict
  detection. Exit: loop-carried pin and the surviving
  exclusivity-family pins reject with their fragments.
  **Landed 2026-07-18.** Loans record their creation loop depth and
  stay live through any deeper loop whatever the syntactic use count
  says — liveness over back edges, the non-lexical-lifetimes lesson
  (RFC 2094) applied to the builder's use-count model. That closes the
  loop-carried hole (`PENDING_REJECTION` is empty: every reject pin in
  the corpus is enforced). The consume-side conflict narrowed to
  exclusive loans per the adjudicated rule; all four exclusivity
  survivors reject with their fragments.
- **E. Escape retains + globals.** Return/global-store/capture
  retains; the global-borrow runtime trap becomes a passing accept
  case. Exit: escape-family pins pass with their new expected outputs.
  **Landed in full 2026-07-19** (branch worktree-drop-elaboration).
  Owning stored views went in on top of drop elaboration, where the
  flip reduced to its true size: the classification change plus one
  consumption rule each way — a bare borrow-typed destination is a
  loan (frames borrow), every stored slot consumes with its declared
  type stripped of borrows (storage owns). Explicit inits borrow their
  borrow params; field stores donate. The whole escape family runs
  with enforced pins, including the global-iterator case; seven corpus
  entries remain parked, all frontend-or-other-surface work. Measured
  against the pre-flip baseline (native instructions, release):
  arith/arrays/fields/calls/dispatch/effects unchanged to ±0.00%,
  strings +1.08% (the honest price of view retains), drops −11.0%,
  grapheme conformance −0.97%, talk-syntax suite +5.61% combined
  compile+run (the parser's large-function planner fixpoints plus
  per-character retain traffic in lexing loops). The reclaim is the
  eager Perceus frontier, which owning views finally make sound
  without provenance tracking; until it lands the suite figure is the
  accepted interim pin. One deliberate re-adjudication: a bare
  `&T` return whose provenance roots at a frame-owned named binding is
  **rejected again** (`returning_borrow_result_of_local_array` pins
  the error). It is the one shape where ownership cannot travel in the
  value without making every bare-borrow-returning call donate
  unconditionally — the caller cannot tell a borrow-of-param return
  from an escaped local, so clone-out would tax core's raw accessors
  on every call. Rejection chosen over that tax; revisit if borrow
  inference ever makes the pair elidable.

  *(Superseded interim note, kept for the record:)* frame-local half
  landed 2026-07-18 — the snapshot family is
  retired. Consuming an owner with a live view retains it; reassigning
  one displaces the old value into an anonymous scope-owned binding
  (the shape of Rust's temporary lifetime extension applied to
  reassignment), with views re-rooted to the displaced value; mutable
  writebacks displace-with-retain instead of invalidating, so a view
  holds its snapshot across a `mut` call; `consume` of a borrowed
  source drains a retained copy; and the Copy/CheapClone gate on
  binding out of a shared borrow is gone (every clone there is a
  retain). Fifteen more pins enforced, with a runtime test pinning
  snapshot values and balance. **Remaining for E:** returning views of
  frame-owned locals and global-rooted views need *owning stored
  views* — a representation change (Borrowed-marker types retaining
  their referents) with bench-pin consequences that gets its own
  design pass; the leftover parked cases besides those are frontend
  work (checker-level Copy/CheapClone bounds, borrowed-element
  pattern typing, capture support) and the dictionary boundaries.
- **F. `talk check` integration.** The analysis runs from the check
  path and the LSP diagnostics surface; `talk check` on a rejected
  program exits nonzero with the same diagnostic `talk run` gives.
  Exit: the review's tooling finding is closed with a CLI-level test.
  **Landed 2026-07-18.** `backend::check` runs MIR construction (the
  ownership analysis, exclusivity, the unsafe gate) without lowering;
  the driver maps a rejection's span back to its document, and the
  check command renders it through the same text/JSON diagnostic
  renderers the frontend uses — located, underlined, schema-identical.
  Every declaration is checked, not just the entry's reachable set.
  The CLI-level test pins check/run agreement. (The LSP still reads
  Workspace diagnostics only; threading the backend analysis through
  the editor surface rides on the same `check_ownership` entry point
  when the LSP work happens.)

Perf guard throughout: the bench corpus's pinned instruction counts
(`bench_bytecode_is_tight`, `bench_corpus_runs`) and the suite-level
counts in `docs/profiling-findings.md` must not regress — retain
traffic added by rule 1 must be paid for by last-use moves, and the
benches are the meter.

## Risks

- **Retain traffic.** Perceus's own evaluation shows inference-placed
  RC competitive with manual ownership; our wave-9 drop machinery
  already does the release half. If a bench regresses, the fix is
  better last-use analysis, not semantic retreat.
- **Snapshot observability.** Escape-then-mutate now yields two
  values where the reference errored. This is the approved change; it
  is also exactly what assignment already does in a value-semantics
  language. The adjudicated pins document each observable change.
- **One-shot continuations.** Retains interacting with captured
  continuation frames need the CFG-fidelity work of wave B/C to land
  first; the effects bench and the handler flow cases pin behavior.
- **Linear types.** Retain placement must never dup a linear value;
  the linear pins stay in the must-reject set from wave A onward.

## Adjudication of the 73 reject pins (wave A, 2026-07-18)

"retired → N" became an accept pinning stdout `N`; "retired → clean"
became an empty pin (runs or compiles clean — the corpus convention,
also used where output rendering isn't knowable until the enabling
wave lands). Retired cases the compiler still rejects or traps on sit
in `KNOWN_STRICTER` until waves C/E; the survivors are enforced now
except `loop_carried_mutable_borrow_lives_until_storage_dead`
(`PENDING_REJECTION` until wave D).

**Survive — exclusivity (4):**
loop_carried_mutable_borrow_lives_until_storage_dead,
move_while_mutably_borrowed_does_not_report_spurious_shared_borrow,
rejects_read_while_mutable_borrow_is_live,
value_borrow_conflicts_still_fire.

**Survive — `&mut` wellformedness (6):**
mut_marker_requires_an_exclusive_parameter,
mut_for_rejects_early_exit_until_commit_is_on_exit,
mut_for_source_through_borrow_is_rejected,
rejects_mut_receiver_call_on_shared_borrow_parameter,
rejects_mut_receiver_call_through_field_of_shared_borrow,
rejects_rvalue_argument_to_a_mut_parameter.

**Survive — linear/unclonable (3):**
linear_value_dropped_at_scope_exit_is_rejected,
linear_value_moved_in_one_branch_only_is_rejected,
unique_parameter_value_moves_like_owned (`*String`: duplicating a
unique pointer breaks uniqueness).

**Survive — declaration wellformedness (5):**
borrow_marker_requires_a_borrowing_parameter,
copy_marker_on_non_cloneable_errors,
rejects_borrow_field_in_unmarked_struct,
rejects_borrow_typed_enum_payload, rejects_borrow_typed_struct_field.

**Survive — heap placement (2):** rejects_heap_in_existential,
rejects_heap_in_raw_storage_container.

**Survive — definite initialization (1):**
rejects_use_before_initializer.

**Survive — unsafe gate (1):** rejects_raw_pointer_usage_in_safe_source
(enforced as of wave A).

**Retired — retain placement, rules 1 and 3 (23):**
retired → 11: array_literal_moves_owned_element,
branch_move_then_use_after_join_is_rejected,
constructor_argument_moves_owned_value,
record_literal_moves_owned_field_value,
rejects_use_after_generic_struct_instantiated_with_owned_field_move,
rejects_use_after_simple_owned_move, tuple_literal_moves_owned_element.
retired → 22: by_value_call_argument_moves_owned_value,
by_value_method_argument_moves_owned_value,
explicit_consuming_method_receiver_moves_owned_receiver,
repeated_owned_call_operand_is_rejected.
retired → 2: move_on_conditional_continue_path_is_use_after_move_on_reentry.
retired → 4: rejects_use_after_struct_with_owned_field_move.
retired → 40: rejects_whole_struct_use_after_owned_field_move (passes
already — the program was always compiled; the reject pin was the
only thing calling it wrong).
retired → 0: repeated_owned_tuple_operand_is_rejected.
retired → clean: consume_for_source_used_after_loop_is_rejected,
consume_marker_forces_a_generic_move, match_arm_move_then_use_is_rejected,
rejects_loop_carried_move_reuse, consume_for_source_through_borrow_is_rejected
(consume through a shared borrow drains a retained copy; the owner is
always protected, so the old rejection guarded an implementation
detail that no longer exists),
rejects_borrowed_loop_element_passed_to_consuming_callback,
move_inside_handler_body_is_may_moved_after,
move_inside_trailing_block_is_may_moved_after.

**Retired — shared-loan snapshot (12):** all → clean:
borrow_of_one_argument_still_rejects_moving_that_argument,
generic_container_containing_borrow_tracks_owner_invalidation,
live_shared_borrow_blocks_later_mutation,
mutable_call_argument_invalidates_shared_borrow,
mutable_method_receiver_invalidates_borrows_of_receiver,
ordinary_borrowed_return_tracks_single_borrowed_argument_owner,
record_containing_borrow_tracks_owner_invalidation,
rejects_borrow_use_after_owner_move,
rejects_borrow_use_after_owner_reassignment,
rejects_match_scrutinee_move_while_borrowed,
rejects_owner_move_while_borrow_has_later_use,
rejects_reassigned_borrow_use_after_owner_move.

**Retired — escape retains (12):** all → clean (declaration-only
except the globals):
borrowed_marker_struct_cannot_escape_its_loan (passes already),
ordinary_borrowed_return_from_owned_local_cannot_escape,
rejects_borrowed_global (passes already),
rejects_function_assigning_a_globally_borrowed_global,
rejects_returning_enum_wrapping_local_substring,
rejects_returning_owned_generic_container_containing_borrow,
rejects_returning_struct_wrapping_local_substring,
rejects_returning_substring_of_local_owned_value,
rejects_returning_substring_of_owned_parameter,
rejects_returning_tuple_containing_local_borrow,
returning_borrow_result_of_local_array_is_rejected,
returning_borrow_through_expression_match_2.

**Retired — cheap-clone bounds at use sites (4):** → clean except
generic_heap_extraction_rejects_non_cheap_owned_instantiation → 0:
borrowed_generic_payload_requires_copy_or_cheap_clone_bound,
rejects_binding_non_cheap_clone_field_from_shared_borrow,
rejects_returning_non_cheap_clone_field_from_shared_borrow.
Under retain-sharing every clone at these sites is a retain, so the
"is the clone cheap?" question these pins policed no longer arises;
`CheapClone` bounds become vestigial at binding/return-from-borrow
sites (the marker itself remains meaningful elsewhere).

## References

- Reinking, Xie, de Moura, Leijen. *Perceus: Garbage Free Reference
  Counting with Reuse.* PLDI 2021.
- Ullrich, de Moura. *Counting Immutable Beans: Reference Counting
  Optimized for Purely Functional Programming.* IFL 2019.
- Matsakis et al. *RFC 2094: Non-lexical lifetimes.* Rust, 2017.
- Weiss, Matsakis, Ahmed. *Oxide: The Essence of Rust.* 2019.
- McCall. *SE-0176: Enforcing Exclusive Access to Memory.* Swift
  evolution, 2017.
- Wadler. *Linear types can change the world!* 1990.
- Kildall. *A Unified Approach to Global Program Optimization.* POPL
  1973.
- Rust MIR drop elaboration and `MaybeInitializedPlaces` (rustc dev
  guide, "MIR dataflow").
- Boissinot et al. *Revisiting Out-of-SSA Translation for Correctness,
  Code Quality, and Efficiency.* CGO 2009 (already the basis of the
  lowering's parallel-copy sequencing).
