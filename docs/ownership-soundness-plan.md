# Ownership soundness: findings and repair plan

Status: all tracks landed (2026-07-12 — track 8.4's fuzzer was the last;
open residuals live in the findings inventory: B11, B12, and F-D below)

## Context

A five-track review of the ownership system (type-level perms/borrows, the
flow pass, drop insertion in lowering, the runtime contract, and
maintainability) confirmed **six memory-safety holes** — programs that pass
`talk check` cleanly and double-free or dangle at runtime — plus seven
lesser bugs and a set of design risks. Every critical finding below was
confirmed with a running repro program (both engines where applicable), not
inferred from reading; each track also reported the suspicions it checked
and cleared, so the sound core is known too: join directions for
moved/initialized state, loop fixpoints, place disjointness, one-shot
continuation accounting, region ledger rules A–F, perm-variable
finalization, Copy-erasure gating, and ADR 0017's bug A (fixed by the
structural temp-drop rewrite) all held up under targeted probing.

The systemic finding is the same one ADR 0017 already made: the invariant
"every owned allocation is freed exactly once per path" is held by a trust
chain (flow trusts types, lowering trusts flow's annotations) with no
verifier behind it. ADR 0017 stage 3 (structural temp drops) landed; stage
2 (the free-balance verifier) and stage 4 (the embedded-body context swap)
never did. Every hole below shipped through that gap, and the only detector
— the evaluator leak fence — covers one engine, scalar-valued programs,
and success paths only.

## Findings inventory

Critical (checker-accepted, memory-unsafe at runtime; all repro'd):

| ID | Finding | Locus |
|----|---------|-------|
| S1 | User `Deinit` on a struct with a droppable field double-frees: the deinit body's own `self` scope-exit drop falls through the recursion guard into structural teardown, duplicating the caller-side glue | `src/lower/statements.rs:396-412` (dynamic twin `:874-889`), guard at `:397-399` |
| S2 | CoW element copy never retains: after `allocate_with_capacity`'s copy loop, two "unique" buffers hold the same element pointers and both deep-drop them (`clone()` + `push` crashes both engines) | `core/Array.tlk:93-105`, reached from `uniqued_storage` (`:83`) and `push` (`:40`) |
| S3 | Pattern binders under borrowed scrutinees are consumable as owned everywhere except direct `take`: the move-out-of-borrow judgment early-returns for root places, skipping the `borrowed_roots` consultation ADR 0025 depends on | `src/flow/loans.rs:279-281`; root check exists only at `src/flow/moves.rs:1350` |
| S4 | `let x: &String = mk()` accepted — the immediate auto-borrow peel runs for every constraint reason, not just `Apply`, so an owned rvalue temp satisfies a borrow annotation (temp drop + alias drop) | `src/types/generate/expr.rs:26-50`, fallthrough at `:234` |
| S5 | Handler and trailing-closure bodies are modeled zero-or-one: no body re-entry edge, so a `consume` inside a body the callee runs twice passes the checker and double-frees | `src/flow/cfg.rs:616-621`; builders at `src/lower/mir.rs:1063-1091`, `:1184-1206` |
| S6 | `MoveState::join_from` merges borrow provenances first-wins instead of union — owner reassignment on the losing path never invalidates the borrower (order-dependent dangling borrow, confirmed with mirror-asymmetric repro) | `src/flow/moves.rs:97-100`; correct pattern ten lines below at `:125-135` |

Bugs (leaks, laundering, false rejections; all repro'd unless noted):

| ID | Finding | Locus |
|----|---------|-------|
| B1 | Aborting effect handlers leak every owned local in the discarded frames (including the installing frame's pre-`@handle` locals and `'heap` region releases); an abort through a finalizer frame also skips the finalizer's remaining frees | `src/lower/effects.rs:203-207`; `talk-runtime/src/interp.rs:273-281` |
| B2 | Early exit (`return`/`break`/`continue`) through an expr-position match arm leaks the enclosing statement's temps; `continue` amplifies per iteration | `src/lower/mir.rs:1437,1446` vs `:958-980`, `:1696-1723` |
| B3 | `Array.set` never drops the overwritten element (it doubles as `push`'s uninitialized-slot writer); `_replace`, which loads the old element, has zero callers. On shared arrays the leak is cancelled by S2's missing retain — they must land together | `core/Array.tlk:52-55`, `:73` |
| B4 | Implicit existential packs launder borrows into owned and defeat linearity (a borrowed `'linear` value returns as an owned `any P` while staying consumable) — ADR 0018's documented gap, confirmed worse than written | `try_implicit_existential_pack`, `src/types/generate/expr.rs:311+` |
| B5 | False rejection: a `consume` generic parameter used in a loop reports use-of-moved because liveness never seeds parameters into `declared`, so last-consume-moves misfires for params but not locals. The wrongly-recorded move is a latent double free if the error were ever suppressed | `src/flow/liveness.rs:74-111` |
| B6 | ADR 0017 bug B is defanged, not fixed: the borrowed-receiver-method for-source shape now fails to compile (`&Array<String>` vs `Array<String>`, reason Pattern) instead of double-freeing. Valid-per-ADR code rejected; stage 5 still open | for-source typing over borrowed-receiver method results |
| B7 | `sort_by` never compares the last element (`j < self.count - 1`); `[1,3,2].sort_by { $0 > $1 }` → `[3,1,2]`. Core's own test passes by coincidence | `core/Array.tlk:121` |

Discovered during wave-2 implementation (pre-existing; status inline):

| ID | Finding | Locus |
|----|---------|-------|
| B11 | Field writes through a scheme-generalized inferred/generic param (`func bump(consume c) { c.count = ... }`) fail at lowering with "not a stored field" — reproduced with owned semantics pre-inferred-params, so pre-existing | lowering of field stores through generic params |
| B12 | `let r = add(1, 2)` can leave the let's captured scheme an unsolved `?N` — final-solve defaulting doesn't reach let-captured schemes | solver final-solve defaulting |
| R9 | **FIXED 2026-07-12.** Calls through function values and witness dispatch now claim the MIR-published unwind entry before lowering nested closures/capabilities and attach it to the application. F-B is the runnable indirect-call repro; `function_value_abort_drops_enclosing_owned_value` balances both engines, with structural witness attachment/no-entry controls in `lower_tests`. | `src/lower/closures.rs`, `src/lower/calls.rs` |

Semantic change flagged for Pat (wave-2 stream 5): corpus case
`types::types_nested_func` (`func fizz(x) { func buzz() { x } buzz() }`)
now errors — implicit closure capture of a borrowed param is rejected.
The annotated twins already rejected identically, so this is the
coherence anchor working, not new strictness; moved to
docs/parity-test-audit.md's deliberate-design-changes list. Revisit if
capture rules should relax for shared borrows.

Discovered during wave-1 implementation (pre-existing, confirmed by minimal
probes while fixing B2; not yet assigned to a track — triage into wave 2):

| ID | Finding | Locus |
|----|---------|-------|
| B8 | A taken string-literal match arm leaks the scrutinee with NO early exit involved: the pattern compiler drops owned occurrences only for **wildcard** cells, so a matched literal arm never frees the occurrence (`match g() { "ab" -> 1, _ -> 2 }` leaks 1 on the taken arm; the `_` arm balances) | `src/lower/patterns.rs:364-376` |
| B9 | A call under a projection never gets a temp: `g().byte_count` leaks standalone — `lower_expr`'s `Proj` arm emits boundary Reads only, the embedded rvalue call gets no MIR Call statement, no temp, no drop candidate | `src/lower/mir.rs` Proj lowering |
| R8 | Temp classification is per-temp static: a temp consumed on the normal path but not on an exit path won't drain on the exit edge (leak-only, never double-free) — verifier corner for Track 6 | `src/flow/cfg.rs` temp classification |
| S7 | Place-read arguments stored into a `'heap` constructor are never buffer-retained: flow's rule-B path records no move and annotates the arg's scope-exit drop Static; lowering emits no `Op::Retain` at the init call. Straight-line double free on unmodified main: `struct Node 'heap { let key: String, ... }` + `let n = Node(key: key, ...)` with `consume key` params crashes both engines. R5/6.3 (retain-walk) territory | flow rule-B / `'heap` init lowering |
| B10 | A body whose tail is a branch join reaches `Terminator::Return` with ScopeExit DropCandidates unclaimed (no ReturnValue statement to run `wrap_cont_with_following_drops`) — owned **parameters** on that shape silently leak (locals survive via StorageDead pairing). The drain fix is written but backed out: it unmasks S7 (double-frees `Dict.insert`'s consume params). Sequencing: land S7's rule-B buffer retain FIRST, then the drain. Documented at `src/lower/mir_lowering.rs:1434-1452` | `src/lower/mir_lowering.rs:1434-1452` |

Discovered by the 8.4 fuzzer (wave 4, 2026-07-12; pre-existing; status
inline, with fixed regressions retained as named tests):

| ID | Finding | Locus |
|----|---------|-------|
| F-A | **FIXED 2026-07-12.** Clone rvalues under borrow arguments and projection receivers now materialize MIR temps with `TemporaryEnd` cleanup. `clone_temp_passed_to_borrow_param_does_not_leak` and `clone_receiver_under_projection_does_not_leak` run on both engines. | `src/lower/mir.rs`; `src/vm/vm_tests.rs` |
| F-B | **FIXED with R9 2026-07-12.** The runnable indirect-call repro now carries the pending unwind entry and balances on both engines (`function_value_abort_drops_enclosing_owned_value`); the direct-call twin remains the control. | `src/lower/closures.rs`, `src/lower/calls.rs` |
| F-C | **FIXED 2026-07-12.** Perform arguments and suspension-capable ordinary-call operands materialize direct aggregate/heap rvalues as well as nested call temps. Object-carrying aggregates qualify even when `needs_drop` is false because Rule B adds a region owner. All are included in unwind candidates and stay caller/performer-owned at runtime. String, Array, `'heap`, and `(Node, Int)` regressions balance on resume/abort across both engines. | `src/lower/mir.rs`, `src/flow/cfg.rs`, `src/lower/mir_lowering.rs` |
| F-D | False rejection: an operator-call result meta (`?N.Ret`) never solves against pattern-position constraints — `match "a" + "b" { "lit" -> …, _ -> … }` and `match Optional.some("a" + "b") { .some(v) -> … }` both reject (`Mismatch reason Pattern` plus a spurious `UnreachableMatchArm`); the `let`-bound twins and declared-function-call scrutinees (B8's shape) compile | solver: Pattern-reason constraints on unsolved call-result metas |

Design risks (no repro found, but not correct by construction):

| ID | Finding | Locus |
|----|---------|-------|
| R1 | Deinit recursion guard keys on (witness, θ), not the value — after S1, a fresh instance created *inside* its own type's deinit silently skips its hook | `src/lower/statements.rs:397-399`, `:874-877` |
| R2 | Loan join dedup ignores permission (shared can swallow exclusive at a join); `borrowed_roots` keeps first perm | `src/flow/moves.rs:87-95`, `:109-114` |
| R3 | `loan_owner_for`/`rebased_perm` consult only the first owning loan of a multi-owner provenance | `src/flow/loans.rs:125-156` |
| R4 | `func f(mut c: &T)` silently drops the `mut` (fails closed with a contradictory diagnostic); unannotated params skip mode application, so stamped `ParamMode::Borrow` and the inferred owned type disagree | `src/types/generate/elaborate.rs:19-22`; `src/types/generate/func.rs:66,178` |
| R5 | Retain walk asymmetric with the drop walk: no `RegionAcquire` counterpart, `CheckTy::Any` falls through with no retain, `rawptr_field_index` stops at the first RawPtr field. Safe only while auto-clone stays gated to Nominal+CheapClone | `src/lower/statements.rs:472-545`, `:650-655` |
| R6 | Non-Static `TemporaryEnd` elaborations silently emit nothing — safe while flow can only produce Static/Dead for temps, a silent leak the day it can't | `src/lower/mir_lowering.rs:346-363` |
| R7 | `instantiate()` substitutes predicates without perms; `ExportSanitizer::fold_perm` defaults `Perm::Var → Shared` store-free (safe only post-`final_ty`) | `src/types/generate/instantiate.rs:82-97`; `src/types/ty.rs:766-771` |

Maintainability and coverage (the conditions that let the above ship):

| ID | Finding |
|----|---------|
| M1 | ADR 0017 stage 2 (free-balance verifier) unbuilt; leak fence is evaluator-only, scalar-only, success-only; VM has `live_count()` but nothing asserts it |
| M2 | Lowering keeps a shadow drop authority: `lower_early_exit_then` merges flow's candidates with `Ctx::drop_stack`, and a missing flow elaboration silently falls through to a type-directed drop (`src/lower/mir_lowering.rs:898-912`, `:966-980`, `:1668-1698`) — ADR 0010 says this was to be deleted |
| M3 | Three sources of truth for a node's type (tree `expr.ty` / `local_tys` / `node_types`) with load-bearing `.or_else()` chains — the exact mechanism behind the already-fixed `seed_arm_binders` bug |
| M4 | Two coexisting Copy judgments (typing's declared grade vs flow's structural `GradeView::is_copy`), undocumented as intentional; four re-spellings of borrow/CheapClone predicates outside `grades.rs` (`src/lower/mod.rs:519-526`, `src/lower/statements.rs:1041-1049`, `src/flow/loans.rs:945-960`) |
| M5 | Flow engine runs its transfer functions three times steered by ambient booleans (`report_errors`/`recording`/`annotate`); top-level bodies checked twice by role convention |
| M6 | ADR 0017 stage 4 unbuilt: `loop_stack`/`handler_stack` hand-swapped per embedded-body site (`src/lower/mir.rs:1076-1089`, `:1200-1204`); enclosing-function early-exit candidates leak into closure bodies, neutralized by classification rather than structure |
| M7 | Doc drift: `moves.rs` header describes deleted `walk_block` machinery; ADR 0017 and 0021 say "proposed" though partly/fully landed; two ADRs numbered 0025; `core-ir-map.md` references a nonexistent `src/hir`; `src/flow/` is the only major module without a README |
| M8 | No property-based/fuzz testing; every recent ownership bug was a combination (closure × temp, borrowed receiver × method × loop) — exactly the class one-instance-at-a-time tests keep missing |

## Decision shape

Fix order follows blast radius and dependency, not discovery order:

1. **Crashers first** (Track 1): S1 and S2 hit ordinary programs — any user
   `Deinit` with a droppable field, any `clone()`-then-mutate. B3 must land
   with or after S2 because today they cancel on shared arrays; fixing
   either alone changes observable balance.
2. **Then the flow lattice** (Track 2): S3/S5/S6 and their design-risk
   siblings are all "the join or the guard is not the lattice operation it
   claims to be" — each has a one-mechanism fix and a ready repro test.
3. **Then the typing gates** (Track 3): S4 and B4 are missing gates on
   existing checks, not new analyses.
4. **Then drop plumbing and the effects abort path** (Tracks 4–5): B2 is
   mechanical; B1 needs a design decision and gets a short ADR.
5. **Then the verifier** (Track 6): ADR 0017 stage 2 back-stops everything
   above and converts this whole bug class from field crashes into red
   tests. It comes after the known bugs because it will refuse to pass
   until they're fixed — landing it first would mean landing it
   pre-suppressed.
6. **Then the single-authority deletions and hygiene** (Tracks 7–8): the
   conditions that minted these bugs. Negative diffs throughout.

Every fix lands TDD: the review's repro program becomes the failing test in
the same change (no `#[ignore]`, no pending markers). The repro corpus also
feeds `tests/programs/` per the confidence plan's Track A2.

## Parallel execution

The correctness tracks (1–5) are mostly mechanism-disjoint; the real
serialization lives in tracks 6–7. Development parallelizes; **landing is
serial**: every wave-1 stream changes accept/reject or drop behavior, so
streams merge one at a time with the full suite run between merges. Each
stream develops in an isolated worktree (the shared test files —
`flow_tests.rs`, `vm_tests.rs`, `lower_tests.rs` — are the main collision
surface) and delivers a patch; merge order within a wave is otherwise
free.

**Wave 1 — ten independent code streams, plus three that don't gate:**

| Stream | Items | Primary files |
|--------|-------|---------------|
| deinit | 1.1 → 1.2 | `lower/statements.rs`, `lower/functions.rs` |
| array-core | 1.3 → 1.4, 1.5 | `core/Array.tlk` |
| join-union | 2.1 + 2.2 | `flow/moves.rs` |
| borrow-root | 2.3 + 2.6 | `flow/loans.rs` |
| body-self-edge | 2.4 | `flow/cfg.rs` |
| liveness-params | 2.5 | `flow/liveness.rs` |
| typing-gates | 3.1 + 3.2 | `types/generate/expr.rs` |
| param-modes | 3.3 | `types/generate/elaborate.rs`, `func.rs` |
| early-exit-temps | 4.1 + 4.2 | `lower/mir.rs`, `lower/mir_lowering.rs` |
| for-source-typing | 8.3 | typing of for-sources |

Non-gating, also wave 1: **5.1's ADR** (design only; implementation waits
for approval), **6.1 verifier scaffolding** (built expecting red — it
should reproduce the known bugs, which validates the verifier itself; not
enabled in CI until wave 1 lands), and **8.1 + 8.2 docs**.

Intra-stream ordering that survives parallelism: 1.2 after 1.1 (same
guard); 1.3 before/with 1.4 (the bugs cancel); 2.1 and 2.2 share
`join_from`; 3.1 and 3.2 share `expr.rs`.

**Wave 2** (after wave 1 lands): enable 6.1; run 6.2's accounting sweep
(it fails on whatever wave 1 missed — that is its job); 6.3 retain/drop
symmetry (deferred from wave 1 because it edits the same `statements.rs`
regions as the deinit stream); 5.1 implementation once the ADR is
approved. Wave-2 triage additions from wave-1 discoveries: **S7 before
B10** (the branch-join drain is written but double-frees `Dict.insert`
until the `'heap`-constructor buffer retain lands — S7 is 6.3/R5
territory); B8 (pattern-compiler literal-arm occurrence drop); B9 (temps
for calls under projections); R8 rides the 6.1 verifier.

**Decisions recorded 2026-07-11 (Pat):** ADR 0027's shape is approved and
mid-finalizer aborts ARE in v1 scope (5.1 implementation is a wave-2
item; flow must model not-yet-freed finalizer fields as live owned
places). **Inferred params really are borrows**: 3.3(b) is re-scoped
from a seeding fix to its own project — apply the stamped mode at
generalization/finalization (post-solve, when Copy erasure is decidable)
or teach the solver deferred borrow constraints (`Borrow(p, ?v) ~ T`,
borrow peeling in HasMember/HasField/operator paths); the pinned
`delayed_auto_borrow_defaults_unresolved_argument_to_owned` semantics
change with it. The wave-1 param-modes report inventories the three
solver gaps (scheme generalization bakes borrows, member resolution on
unsolved borrowed receivers, deferred Copy erasure).

**Wave-2 execution note (2026-07-11)**: wave 1 is integrated but
uncommitted in the main tree, so worktrees (which fork from HEAD) can't
see it — wave 2 runs SEQUENTIALLY in the main tree, one stream at a
time, which is the serial-landing protocol anyway. Order: (1) 6.3+S7,
then B10 in the same stream (S7 gates B10); (2) B8; (3) B9; (4) 6.2
accounting sweep + 6.1 enablement (after B8/B9 so the sweep isn't
drowned by known leaks); (5) ADR 0027 implementation; (6) the
inferred-params-are-borrows project. A snapshot of the integrated
wave-1 state lives in the session scratchpad (wave2/
wave1-integrated-*.patch). If wave 1 gets committed mid-wave, later
streams can parallelize into worktrees again.

**Wave 3, one at a time**: track 7's refactors are broad and mechanical —
7.2 rewrites the `cfg.rs`/`moves.rs` that track 2 just touched, 7.4 and
7.5 sweep across `mir.rs`/`moves.rs`/`statements.rs`. Concurrency here
buys merge pain and no time. Hard edges: 7.1 requires 6.1 live (the
verifier is what makes deleting the drop-stack fallback safe); 7.3
requires 4.1 (it bundles the temp vecs 4.1 introduces).

**Wave 4**: 8.4's fuzzer, with 6.1 + 6.2 as its oracle.

## Track 1 — runtime crashers

**1.1 (S1) Deinit glue owns field teardown; the body owns none.**
The invariant is the one Swift implements: the compiler-synthesized
deinitialization (field releases) runs *after* the user's `deinit` body,
and only the compiler emits it. Fix locus is the recursion guard in
`lower_drop_value_then` (`statements.rs:397-399` and the dynamic twin):
when the guard suppresses hook re-dispatch for the deinit body's own
`self`, it must elaborate to a **no-op**, not fall through to
`lower_structural_teardown_then`. Keying: suppress structural teardown only
for the `self` place of the enclosing deinit body (see 1.2), not for every
value of the same (witness, θ). While here, chase the open inconsistency:
core `Array<Element>: Deinit` somehow already escapes body-side teardown
(its lowered body contains only element frees) and the suppression
mechanism could not be located — find it, and either generalize it or
delete it in favor of the guard fix so there is one mechanism.
*Tests first:* the 12-line `Loud { s: String }` repro on both engines; a
generic `Loud<T>` instantiated at `String`; a deinit whose body reads a
field then returns. Done when all pass balanced and the existing
scalar-field Deinit tests still pass.

**1.2 (R1) Re-key the recursion guard on the value, not the type.**
After 1.1, `ctx.owner != Some(witness) || value_theta != ctx.theta` still
suppresses the hook for *any* same-instantiation value inside a deinit
body, so a fresh `Loud` local created inside `Loud.deinit` skips its own
destructor. Mark the deinit body's `self` local explicitly (a flag on the
`DropBinding` built at `functions.rs:126-155`) and key the guard on that.
*Test first:* a deinit that constructs and drops a sibling instance;
assert both hooks' side effects appear.

**1.3 (S2) CoW copies retain their elements.**
Swift's precedent: a CoW buffer copy is a *copy*, so element references
are retained as they are written into the fresh buffer; uniqueness is
re-established per buffer, not shared by fiat. In
`allocate_with_capacity`'s copy loop, retain each copied element when the
source buffer survives the copy (the `uniqued_storage` CoW path). The
`push` grow path from an already-unique buffer is a *move* — no retains,
but the old buffer's shell must be freed without deep-dropping the
elements it just donated. If the copy loop can't distinguish callers,
split it: `copy_retaining` (CoW) vs `move_into` (grow).
*Tests first:* the `clone()`+`push` repro; `clone()`+`set`; grow past
capacity with droppable elements (no leak, no double free); nested
`[[String]]` versions of each. Both engines, balance asserted.

**1.4 (B3) `set` drops the overwritten element; the raw writer goes private.**
Revive `_replace` (currently zero callers): public `set` loads and drops
the old element (or returns it, Swift `Dictionary.updateValue`-style),
and the uninitialized-slot write used by `push` becomes a private
`_init_slot`. Must land with or after 1.3 — today the two bugs cancel on
shared arrays.
*Tests first:* overwrite a droppable element in owned and in shared
(post-`clone`) arrays; balance both.

**1.5 (B7) `sort_by` last element.**
`j < self.count - 1` → `j < self.count` at `core/Array.tlk:121`.
*Test first:* `[1, 3, 2].sort_by { $0 > $1 } == [3, 2, 1]` — a case where
the last element must move.

## Track 2 — flow lattice repairs

**2.1 (S6) Union provenances at joins.**
`MoveState::join_from` merges `provenances` first-wins; make it union via
`Provenance::union_with` exactly as `temp_provenances` already does ten
lines below. Precedent: NLL computes in-scope loans by forward dataflow
over bitsets — the join is set union, never first-predecessor-wins.
*Tests first:* the confirmed repro (borrow reassigned on one branch,
owner reassigned after the join) **and its mirror** — the mirror currently
passes/fails asymmetrically, which pins the order-dependence.

**2.2 (R2) Loan dedup includes the permission.**
Same family: the join dedup key at `moves.rs:87-95` is (borrower, owner) —
add the loan kind so a shared loan can't swallow an exclusive one; union
perms in `borrowed_roots` weakest-wins (shared) only when both paths agree
the root is borrowed at all. No surface repro exists today; the test is a
unit test on `join_from` directly (both orders, assert the joined state is
order-independent — that property, `join(a,b) == join(b,a)`, is worth
asserting for the whole `MoveState` while here).

**2.3 (S3) Root places consult `borrowed_roots` in the move-out-of-borrow judgment.**
`check_move_out_of_borrowed_with` opens with
`if place.fields.is_empty() { return false }`. Replace the early return
with the same root-place consultation the `take` path already does
(`moves.rs:1350`): a root binder registered in `borrowed_roots` is
borrowed storage, and consuming it must either tier-2 auto-clone
(CheapClone payloads — these programs should compile-with-retain, not
error) or reject.
*Tests first:* the four confirmed shapes — return position, aggregate
construction, tuple-nested pattern, `consume`-argument — each asserted to
either error or balance; plus the CheapClone-payload version asserted to
compile and balance via retain.

**2.4 (S5) Handler and trailing-closure bodies get a re-entry edge.**
`Terminator::Handler` successors gain a body self-edge (feed the body's
exit state back into its own entry), making these bodies loop-shaped: a
move inside the body is may-moved at the body's entry, exactly how loop
back-edges already reject loop-carried moves. **Novel-departure flag:**
this is a deliberate approximation — "the body may run any number of
times" — chosen over tracking callee invocation counts; OCaml sidesteps
the question by making continuations linear at runtime, which Talk's VM
already enforces per continuation but not per handler-body *entry*. The
approximation direction is sound (rejects more), and CheapClone consumes
inside bodies keep compiling via auto-clone.
*Tests first:* both confirmed repros (handler performing twice;
`run_twice { take(s) }`) asserted to error; a body that consumes a
CheapClone value asserted to still compile; the existing
`move_inside_handler_body_is_may_moved_after` covers the join half.

**2.5 (B5) Liveness seeds parameters.**
Seed `declared` with the body's parameter symbols (position 0) in
`Liveness::analyze` so the loop-carry invariant ("loop-carried uses extend
to the loop end") holds for params, not just locals.
*Tests first:* the confirmed repro (generic `consume` param eaten inside a
loop) asserted to compile with auto-clone; its local-variable twin already
passes and pins the asymmetry.

**2.6 (R3) Fold over all owning loans.**
`loan_owner_for`/`rebased_perm` take the first owner of a multi-owner
provenance; make them fold over all owners (conflict if any owner
conflicts, perm = weakest across owners). Unit-test with a hand-built
two-owner provenance; no surface repro exists (install-time checks shadow
it today) — that's the point of fixing it before one does.

## Track 3 — typing gates

**3.1 (S4) The immediate auto-borrow peel is Apply-only.**
`check_expr`'s expected-Borrow branch and `emit_immediate_borrow_check`
run for every constraint reason; gate them on `Apply` (and the existing
covariant-return site), so a `let`/annotation reason demands a genuine
borrow. The flow pass needs no compensation — an owned rvalue no longer
reaches a borrow-annotated binder.
*Tests first:* `let x: &String = mk()` rejected; `let x: &String = s`
(borrow of a local) still accepted; call-site auto-borrow unaffected
(existing corpus).

**3.2 (B4) Implicit existential packs go through the borrowed-return check.**
Route `try_implicit_existential_pack` through the same
ownership/borrowed-return judgment every other return path gets; packing
from a borrowed source either retains (CheapClone), errors (linear or
uniquely-owned payloads), or requires an explicit consume. This closes
ADR 0018's documented "known gap" — update that ADR's residuals section
when it lands.
*Tests first:* the `'linear` Socket repro rejected; a CheapClone payload
pack asserted to balance; an owned (consumed) pack still accepted.

**3.3 (R4) Parameter modes conflict loudly and apply universally.**
Two halves: (a) `apply_param_mode`'s `Ty::Borrow(..) => ty` arm becomes a
declaration-site error when the mode is `mut`/`consume` and the annotation
already spells a borrow (`func f(mut c: &T)`) — today it silently drops
the mode and the user gets a contradictory downstream diagnostic; same for
`(mut &T) ->` function types in the parser path. (b) Unannotated params
(`func f(x)`) wrap their fresh var per the stamped mode
(`Borrow` default), so the stored `ParamMode` and the solved type agree —
today inference produces an owned param the mode says is borrowed, a trap
for anything keyed on mode (inout write-back selection, LSP hover).
*Tests first:* declaration-site error for `mut c: &T`; inferred-param
program whose caller can reuse the argument after the call (borrow
semantics observable), which currently move-errors.
**(b) LANDED 2026-07-12** (wave-2 stream 6): `infer_callable` routes the
fresh var through `apply_param_mode`; the solver gained deferred Copy
erasure (`&?v ~ Nominal` in unify, plus shared-Copy-borrow erasure at
finalize), HasMember residuals peel borrowed receivers when qualifying
schemes, the record-improvement probe binds the peeled receiver, and
flow's `call_provenance` learned the protocol-static callee shape.
Staged out: inference-position trailing-block binders stay
delayed-inference (see ADR 0018 implementation notes);
`types_nested_func` moved to parity-test-audit.md's
deliberate-design-changes list.

## Track 4 — drop insertion

**4.1 (B2) Early exits drain enclosing pending temps.**
An arm-level `return`/`break`/`continue` drains only its own statement's
temps; the enclosing match's scrutinee/result temps (pushed at
`mir.rs:1437,1446` for the join block) leak. Single-authority fix: thread
the enclosing statement's pending-temp vec into `emit_early_exit_drops` so
every early-exit terminator drains all temps accumulated from the
innermost statement out to the exit's target scope — same data the join
block uses, emitted on the exit edge instead. (Alternative — giving temps
places so flow's `EarlyExit` candidates cover them — is bigger and can
ride Track 6's verifier follow-ups if the threading proves fragile.)
*Tests first:* the three confirmed repros (`return` in taken arm; `break`;
`continue` × 3 iterations asserting exactly-zero leaks); untaken-path
variants stay balanced; same shapes through expr-position `if` and
short-circuit operators.

**4.2 (R6) Non-Static temp elaborations become a diagnostic.**
`mir_lowering.rs:346-363`: a `TemporaryEnd` candidate with any elaboration
other than Static/Dead is an internal error (debug assert + lowering
diagnostic), not silence. Zero behavior change today; converts a future
silent leak into a loud one.

## Track 5 — the effects abort path (needs a short ADR)

**5.1 (B1) Aborting handlers run the suspended frames' drops.**
Today an aborting handler returns through `raw_ret_k` and the VM's
`CallCont` unwind discards frames wholesale — every owned local in every
discarded frame leaks, including the installing frame's own pre-`@handle`
locals and `'heap` region releases; an abort through a finalizer frame
also abandons the finalizer's remaining frees (`interp.rs:276-278`).

Precedent: OCaml requires captured continuations be consumed exactly once
— `continue` or `discontinue` — and `discontinue k e` exists precisely so
the suspended stack unwinds *through its cleanup* rather than being
dropped; relying on GC finalizers to do it is documented as the fallback,
not the design. Talk already has the per-frame cleanup code — every
function's early-exit drop machinery — it just never runs on this path.

Recommended design (**flag: novel composition, needs the ADR**): implement
abort as *discontinue* — the VM, instead of discarding frames, resumes the
continuation one last time into a per-function **unwind entry**: a block
the lowerer already knows how to emit (the function's scope-exit drops for
all currently-live locals, then propagate the unwind to the caller frame).
This keeps the "lowering emits, runtime executes" split: no runtime drop
tables, no VM knowledge of types; the finalizer-frame case falls out
because the finalizer's own frame unwinds through its remaining frees.
The alternative (VM-side per-frame drop tables interpreted at unwind time)
duplicates drop authority into the runtime and is rejected on the
no-second-authority principle. Liveness at the perform site selects which
locals the unwind entry drops — the same Conditional drop-flag machinery
statement-position drops already use.
*Tests first:* the three confirmed leak shapes (owned array in performer's
frame / intervening frame / installing frame), each asserted balanced
after an abort; a `'heap` object across an abort (region released); an
abort during a finalizer (remaining fields freed); resumed-handler paths
unchanged (existing corpus).

## Track 6 — the verifier and accounting (ADR 0017 stage 2, at last)

**6.1 Build the free-balance verifier.**
As ADR 0017 specifies: a post-lowering pass over λ_G (alongside the
existing typing/WF verifier in `src/lambda_g/check.rs`) that checks every
owned allocation is freed exactly once per path, using the same
Static/Dead/Conditional/Open classification rustc's drop elaboration
uses (`MaybeInitializedPlaces`/`MaybeUninitializedPlaces`-style facts —
Talk's flow pass already computes the equivalents; the verifier re-derives
balance *independently* from the emitted IR, which is what makes it a
check rather than a third authority). Perceus's "garbage-free" theorem is
the formal shape of the claim being verified: precise RC programs neither
leak nor double-free by construction — the verifier is the mechanized
version of that argument for Talk's lowered output. Runs in debug/test
builds on every lowered body.

**6.2 Close the accounting blind spots.**
(a) `run_vm_with_output` asserts `live_count()`/`live_objects()` after
every VM run — the counter exists, nothing reads it. (b) The evaluator
leak fence extends past scalar results: assert balance for
container/String-valued programs by draining the result value before the
check. (c) Error-path runs (checker-rejected programs never execute, but
runtime traps should still report balance-at-trap for diagnosis).
The first sweep will fail on every bug in Tracks 1–5 that hasn't landed
yet — that's the sequencing argument for doing this track sixth.

**6.3 Retain/drop symmetry (R5).**
Make the asymmetries in `lower_retain_value_then` structural: add the
`RegionAcquire` counterpart to the drop path's `RegionRelease`, make
`CheckTy::Any` retain via the existential witness exactly as the drop
path dispatches it, and fix `rawptr_field_index` (both walks) to handle a
RawPtr field *plus* other droppable fields. Add a unit test asserting the
two walks visit the same field set for a struct with mixed
RawPtr/droppable fields. This is what makes widening auto-clone safe later.

## Track 7 — single-authority deletions

Each of these deletes a mechanism that generated or masked a Track 1–5 bug.
All are negative diffs.

**7.1 (M2) Delete lowering's shadow drop authority.**
Flow emits `EarlyExit` candidates covering the standalone-body path so
`lower_early_exit_then`'s drop-stack remainder loop is deleted; the
`Some(Static) | None =>` fallthroughs become diagnostics (a candidate flow
failed to classify is an internal error, not a guess). ADR 0010 already
mandates this; Track 6's verifier makes it safe to do.
**LANDED 2026-07-12** (wave 3): instrumentation across the full suite
showed the remainder loop already dead — waves 1-2 (early-exit temps,
B10's unclaimed-drop drain, ADR 0027 unwind entries) left no shape it
still covered — so it was deleted outright along with its plumbing
(`stack_from`, `LoopBinding::drop_depth`, `lower_drop_bindings_then`,
`lower_dynamic_drop_binding_then`); both `None` fallthroughs
(`lower_candidate_drop_then`, `lower_mir_storage_dead`) now diagnose +
debug-assert and emit nothing (leak-safe; flow classifies every
needs-release candidate including generic ones, so no sanctioned `None`
exists at either site — the pre-monomorphization carve-out elides on the
elaborated candidate's concrete type, not via missing elaborations).
`Ctx::drop_stack` survives only as value-level candidate metadata
(symbol → concrete type / drop-flag keys / deinit-self), documented as
such. Six early-exit characterization tests pin the shapes in
`lower_tests.rs`.

**7.2 (M5) The flow engine's three passes take a `Pass` enum.**
Replace `report_errors`/`recording`/`annotate` ambient booleans with one
explicit `Pass::{Fixpoint, Record, Report}` parameter threaded through
`transfer_block`/`transfer_statement`, deleting the save/restore
choreography at `cfg.rs:43-87`. Mechanical; makes the mode contract
type-visible.
**LANDED 2026-07-12** (wave 3): `Pass` lives in `cfg.rs` (doc comment
pins its relationship to `BodyRole` — role picks the passes, pass steers
the side effects); `transfer_block` takes it as a parameter and mirrors
it onto `MoveChecker.pass` (the single mode field replacing
`report_errors` + `recording`) for the deep transfer walks in
`moves.rs`/`loans.rs`, so terminator edge effects inherit it too. The
save/restore is gone; `check_bodies` ends by resetting the checker to
its documented resting mode (`Report` — `check_flow`'s pre/post passes
are error-only walks, also the constructor default). `error()` matches
exhaustively so a future fourth pass reports nothing by default.
Runtime-transfer policy stays orthogonal to pass phasing. Source moves now
update source availability independently from runtime transfers: effect
payloads and +0 object parameters retain cleanup while becoming unavailable
to source. +0 parameters are runtime-borrowed within the callee, so field
moves retain or reject rather than aliasing caller-owned teardown. The old
overlapping temp sets are one `TempOwnership` map, including conditional
object cleanup that survives generic specialization. Named places and temps
share an initialization-order domain for unwind ordering. A characterization
test pins top-level errors reporting exactly once under the
twice-checked role convention
(`flow_tests.rs::reports_top_level_flow_error_exactly_once`).

**7.3 (M6) ADR 0017 stage 4: `lower_embedded_body`.**
Bundle the statement-scoped builder fields (`loop_stack`,
`handler_stack`, per-statement temp vecs, and — after 4.1 — the
enclosing-temp linkage) into one context struct swapped wholesale at the
two embedded-body sites. Also scope `scope_stack` so a `return` inside a
trailing block stops minting early-exit candidates for the *enclosing
function's* locals (currently neutralized by classification, not
structure).
**LANDED 2026-07-12** (wave 3): `StatementScope` in `mir.rs` bundles
`loop_stack`, `handler_stack`, `continuation_temps`, `join_depth`,
`block_value_temps`, `enclosing_temps`, `root_tail_is_return`, and the
new `scope_floor`; `Builder::lower_embedded_body` is the one way in
(handler site passes the resume join, trailing site passes none) and
swaps the bundle wholesale via `mem::replace`. The `scope_floor` clamp
in `emit_early_exit_drops` (and `loop_scope_depth`'s fallback) makes the
early-exit isolation structural; a MIR test pins it
(`return_inside_trailing_block_mints_no_early_exit_for_enclosing_locals`).
Swapping the previously-unmasked fields fixed a real bug the old
per-field discipline had missed, exactly per the ADR's thesis:
`block_value_temps` leaked into trailing bodies, so a trailing block's
value tail inside a block expression delivered to the ENCLOSING block's
temp and λ_G construction panicked (T-App domain mismatch) — pinned
fixed by `trailing_block_tail_inside_value_block_returns_to_its_own_caller`
(vm_tests, plus the `continuation_temps` match-arm twin). Two full-bundle
characterization tests (trailing block + handler body, both engines,
balance-asserted) landed first. `pending_unwind` (ADR 0027) was checked
and stays out: it lives on the λ_G lowerer, scoped per call-evaluation
statement, not on the MIR builder. `@handle` still only lowers at a
body's root (nested-block fence), so no enclosing loop/temp statement
can surround the handler site today.

**7.4 (M3) One authority per type question.**
"Expression type" = the typed tree; "binder type" = `local_tys`. Make the
accessors enforce it and delete the `.or_else()` fallback chains over
`node_types` (`mir.rs:406,618,1113,1168,1221`, `moves.rs:383`,
`cfg.rs:581`). `node_types` shrinks to whatever genuinely has no tree home
— if that set is empty, it's deleted.
**LANDED 2026-07-12** (wave 3): instrumentation across the full suite
first established the key structural fact — typing writes `node_types`
for expression and parameter nodes ONLY (pattern binders go to `mono` →
`local_tys`), and the build bakes exactly that map onto the tree as
`expr.ty`/`param.ty` — so every per-node fallback reached with a binder
id or behind a baked tree field was PROVABLY dead (zero fires: the
binder arms in `arm_release_binders`, the former temp-unwind builder path,
`cfg.rs local_ty`, `check_let` ×2, `check_global_storage`, and the
param arms in `owned_param_locals`/`seed_params`/`lower_function` —
including their scheme-params third arms, all deleted along with the
now-unneeded `owner`/`func_ty`/`signature_params` plumbing). The ONE
live arm was `lower_expr`'s Call `result_ty` map read, which leaked
typing-internal effect args (`Ty::Eff` on nominal heads) into MIR
`result_ty` where the tree's baked type is erased — all 128 suite
firings differed by exactly `erase_eff_args`; it now reads `expr.ty`
(Block/Perform twins too), suite + verifier + both fences green, so the
raw flavor was demonstrably inert. `TypeOutput::binder_ty(symbol)` is
the one binder accessor (`local_tys` behind it, doc-pinned);
`node_types`' field doc now names its only two sanctioned consumers
(typed-tree bake, IDE surfaces over the surface AST) plus the one
flow-side residue (clone-fact rendering in `flow/mod.rs`, display-only,
bare ids in hand). The map itself stays — it IS the carrier the tree is
built from — but flow/lowering no longer touch it, and
`types_tests.rs::binder_types_live_in_local_tys_not_node_types` pins
the invariant that makes the deleted fallbacks unrepresentable. The
`seed_arm_binders` warning comment reduced to the pattern-viewing note.
Found (not fixed, bug-for-bug): `check_let`'s header claimed
"destructuring binders carry their own node types" — that arm never
fired, so destructuring and uninitialized binders have always
classified via `Ty::Error` (comment corrected to say so); switching
them to `binder_ty` is a real semantic change left for its own change.

**7.5 (M4) One spelling per ownership predicate.**
Route `symbol_has_conformance`'s CheapClone check and
`symbol_is_borrowed` through `GradeView`; fold `loans.rs`'s
`stores_borrow` into a `grades.rs` walk. Document, in the `grades.rs`
header, that typing's declared-grade Copy and flow's structural
`is_copy` answer different questions (coercion legality vs move-on-use)
with one example — so nobody "unifies" them and silently changes
semantics. The pre-monomorphization needs-drop carve-out is the one
sanctioned dual; it moves into the flow README (8.1) as such.
**LANDED 2026-07-12** (wave 3): the three named spellings are gone —
`symbol_has_conformance` deleted outright (`auto_clone_action_for_ty`
asks `is_cheap_clone_type`, a `grade_views()` wrapper over
`GradeView::is_cheap_clone` beside `needs_drop_type`), lowering's
`symbol_is_borrowed` delegates to the new
`GradeView::symbol_is_borrowed_value` (the symbol-level twin
`is_borrowed_value` now shares), and `stores_borrow` moved verbatim
into `grades.rs` with its deliberate difference from
`contains_borrowed` documented (syntactic declaration-position check:
`Borrowed`-marker nominals are storable, nominal fields were checked at
their own declaration). The audit found and routed three more:
`check_borrow_storage`'s two raw `has_bare_conformance(_, Borrowed)`
reads (`loans.rs`), `moves.rs::ty_is_linear` (now
`GradeView::is_linear`, which `contains_owned`'s linear clause shares),
and lowering's `symbol_is_heap` + `demand.rs`'s inlined copy (now
`GradeView::symbol_is_object`, which `is_object` shares). Every raw
classification read of the catalog in `lower/` and `flow/` now lives
inside `grades.rs`. Left with reason: `deinit_witness`/`deinit_theta`
fetch conformance VALUES (witness symbol, self-args θ), not a
classification; perm reads/borrow peels (`Ty::Borrow(perm, _)`
matches) ask "which permission", not "is it borrowed"; wave-2's
`auto_clone_action_for_ty` is per-instantiation policy COMPOSED of
GradeView judgments, not a new spelling. The declared-vs-structural
Copy split is documented in the `grades.rs` header with the `Point`
example; the sanctioned pre-monomorphization dual was already in the
flow README (8.1).

**7.6 (R7) Perm hygiene.**
`instantiate()` substitutes perms into predicates alongside tys/effs/rows;
`ExportSanitizer::fold_perm` gets a debug assertion that it only ever sees
post-`final_ty` types (or is changed to resolve through the store). Both
latent-only; both one-liners plus a unit test each.
**LANDED 2026-07-12** (wave 3): `Predicate::substitute_perms` (the
mirror of `Ty::substitute_perms`) now chains after `.substitute(..)` at
BOTH instantiation sites — `generate/instantiate.rs::instantiate` and
its solver twin `solve/member.rs::instantiate_scheme`, which had the
identical hole. The five near-identical per-variant matches on
`Predicate` collapsed into one `fold_with(TyFold)` owner
(`substitute`/`substitute_perms`/`sanitize_for_export`/`import_symbols`
are one-liners over it). Both holes confirmed LATENT: `Perm::Var` has
no generation-phase producer — vars are minted only when instantiating
a scheme that already has `perm_params`, and `generalize.rs` mints
those only upon seeing a `Perm::Var` — so no source program reaches
either path today; the unit test hand-builds a perm-quantified scheme
whose predicate mentions the param and asserts the instantiated
predicate carries the SAME fresh var as the scheme type
(`solve/tests.rs::instantiation_substitutes_perms_into_predicates`).
`ExportSanitizer::fold_perm`'s `Var → Shared` arm got the contract
pinned as a comment + `debug_assert!`: `final_ty` runs
`default_unsolved_perms` (binding every unsolved perm var to Shared in
the store), so finalized input contains NO `Perm::Var` and the arm is
belt-and-suspenders — on pre-finalize input the store-free rewrite
would launder a solved-to-Exclusive var to a shared borrow. The
assertion held over the full suite (empirically: every sanitize path is
post-finalize or perm-var-free), and
`export_sanitizer_rejects_unfinalized_perm_vars` pins that it fires.

## Track 8 — hygiene and the long tail

**8.1 `src/flow/README.md`.**
The layer that owns every ownership judgment is the only major module
without a README. It centralizes the three cross-layer contracts currently
scattered in comments (lowering does not re-analyze ownership; GradeView
agreement; embedded-copy fact mirroring) plus the sanctioned
pre-monomorphization dual from 7.5.

**8.2 Doc drift.**
Fix the `moves.rs` header (`walk_block` is gone); set ADR 0017's status to
"partially landed" with a stage checklist (this plan closes stages 2, 4,
5); set ADR 0021 to "implemented"; renumber one of the duplicate 0025s;
update `core-ir-map.md`'s `src/hir` references to
`src/typed_ast`/`src/compiling/typed_program`; record B4's fix in
ADR 0018's residuals.

**8.3 (B6) ADR 0017 stage 5: the borrowed-receiver for-source.**
The typing hunt the ADR scoped: the for-loop binder over a
borrowed-receiver method's result types owned (`Array<String>` where
`&Array<String>` arrives, reason Pattern). Now merely a false rejection,
so it sits last among the correctness items; the free-function-source twin
that compiles pins the receiver-path locus.
*Test first:* the ADR's fs-walk shape compiles and balances on both
engines (replacing the current string-presence assertion at
`lower_tests.rs:417-421`, which never executes the program).

**8.4 (M8) A grammar-restricted program fuzzer.**
After 6.1/6.2, a small generator over the ownership-relevant grammar
(lets, borrows, consumes, loops, closures, handlers, matches, arrays,
heap structs) whose only oracle is: compiles ⇒ verifier passes ⇒ both
engines agree ⇒ zero live allocations. This is differential testing in
the McKeeman sense, which the eval≡VM suite already practices — the
generator just walks the combination space (closure × temp,
borrowed receiver × method × loop, handler × consume) that every recent
ownership bug lived in and hand-written tests keep sampling one point of.
Seeded, deterministic in CI; failures shrink to corpus entries in
`tests/programs/`.
**LANDED 2026-07-12** (`tests/fuzz.rs`, a dedicated Cargo test target gated
by the `fuzz-tests` feature, which also enables the balance verifier and VM
fence in the oracle): typed grammar
with a scope stack (owned/borrowed/consumed tracking; loop, for, and
closure bodies are consume barriers; ~10% "spice" deliberately violates
the tracking to keep the reject path populated), hand-rolled xorshift64*
+ splitmix64 per-program seeds, greedy tree shrinking
(remove/unwrap/zero ops re-running the oracle), failures written to
`target/fuzz/`. CI runs 60 programs at a fixed base seed in ~7s at an
88% compile rate (floor asserted at 60%). Run it with
`cargo test --test fuzz --features fuzz-tests`; `TALK_FUZZ_SEED` /
`TALK_FUZZ_COUNT` / `TALK_FUZZ_SHRINK_BUDGET` drive exploratory runs,
`TALK_FUZZ_PROBE` runs one file through the exact oracle with per-engine
leak attribution. First session (5,000+ generated programs) found
findings F-A/F-B/F-C/F-D above — every failure shrank to one of those
four roots. F-A, F-B/R9, and F-C are fixed and retained as named
regressions; the R9/F-B and F-C default-seed skips (indices 67 and 155)
were removed, and `DEFAULT_SKIPS` is empty. F-D remains an open checker
false rejection and is not a runtime-oracle skip.

## Citations

Per-decision prior art, verified 2026-07-11:

- **1.1 glue-owns-field-teardown**: Swift's deinitialization model — the
  user `deinit` body runs first, then compiler-synthesized code releases
  stored properties; user code never re-frees fields.
  [Swift book: Deinitialization](https://docs.swift.org/swift-book/documentation/the-swift-programming-language/deinitialization/),
  [SE-0371 discussion of compiler-generated deinitialization](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0371-isolated-synchronous-deinit.md).
- **1.3 CoW copies retain**: Swift stdlib CoW — uniqueness via
  `isKnownUniquelyReferenced`, copies performed as real copies of element
  references before mutation.
  [Jared Khan, Swift's copy-on-write](https://jaredkhan.com/blog/swift-copy-on-write),
  [Why Swift's CoW is safe](https://mjtsai.com/blog/2019/02/06/why-swifts-copy-on-write-is-safe/).
- **2.1 loans/provenance union at joins**: NLL computes in-scope loans by
  forward dataflow with set-union joins.
  [RFC 2094 (NLL)](https://rust-lang.github.io/rfcs/2094-nll.html),
  [rustc-dev-guide: the borrow checker](https://rustc-dev-guide.rust-lang.org/borrow-check.html).
- **5.1 abort runs cleanup (discontinue)**: OCaml's one-shot continuations
  must be consumed exactly once; `discontinue k e` unwinds the suspended
  stack through its cleanup, and finalizer-based unwinding is explicitly
  the fallback, not the design.
  [OCaml manual: Effect handlers](https://ocaml.org/manual/5.5/effects.html),
  [Sivaramakrishnan et al., Retrofitting Effect Handlers onto OCaml](https://arxiv.org/pdf/2104.00250).
- **6.1 verifier shape**: rustc's drop elaboration —
  Static/Dead/Conditional/Open classification from
  `MaybeInitializedPlaces`/`MaybeUninitializedPlaces`, drop flags for the
  conditional cases.
  [rustc-dev-guide: drop elaboration](https://rustc-dev-guide.rust-lang.org/mir/drop-elaboration.html).
  The balance property itself is Perceus's "garbage-free" theorem for
  precise reference counting.
  [Reinking, Xie, de Moura, Leijen — Perceus (PLDI '21)](https://dl.acm.org/doi/10.1145/3453483.3454032).
- **Novel departures** (no direct prior art, flagged above): 2.4's
  body self-edge as an "unbounded re-entry" approximation for handler and
  trailing-closure bodies (loops-shaped treatment rather than invocation
  counting); 5.1's composition of discontinue-style unwinding with
  lowerer-emitted per-function unwind entries selected by perform-site
  liveness (keeps drop authority out of the runtime).

## Exit criteria

- All repro programs from the review run balanced (or are rejected with a
  correct diagnostic) on both engines, as committed tests.
- The free-balance verifier runs on every lowered body in test builds; VM
  runs assert `live_count()` balance.
- `lower_early_exit_then`'s drop-stack remainder loop, the `None` drop
  fallthroughs, the three ambient flow booleans, and the `.or_else()`
  type-lookup chains no longer exist.
- ADR 0017 has no open stages; ADR 0018's existential-pack gap is closed
  and its residuals updated; the fuzzer runs seeded in CI.
