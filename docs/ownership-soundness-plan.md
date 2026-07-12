# Ownership soundness: findings and repair plan

Status: proposed (2026-07-11)

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

Discovered during wave-1 implementation (pre-existing, confirmed by minimal
probes while fixing B2; not yet assigned to a track — triage into wave 2):

| ID | Finding | Locus |
|----|---------|-------|
| B8 | A taken string-literal match arm leaks the scrutinee with NO early exit involved: the pattern compiler drops owned occurrences only for **wildcard** cells, so a matched literal arm never frees the occurrence (`match g() { "ab" -> 1, _ -> 2 }` leaks 1 on the taken arm; the `_` arm balances) | `src/lower/patterns.rs:364-376` |
| B9 | A call under a projection never gets a temp: `g().byte_count` leaks standalone — `lower_expr`'s `Proj` arm emits boundary Reads only, the embedded rvalue call gets no MIR Call statement, no temp, no drop candidate | `src/lower/mir.rs` Proj lowering |
| R8 | Temp classification is per-temp static: a temp consumed on the normal path but not on an exit path won't drain on the exit edge (leak-only, never double-free) — verifier corner for Track 6 | `src/flow/cfg.rs` temp classification |
| S7 | Place-read arguments stored into a `'heap` constructor are never buffer-retained: flow's rule-B path records no move and annotates the arg's scope-exit drop Static; lowering emits no `Op::Retain` at the init call. Straight-line double free on unmodified main: `struct Node 'heap { let key: String, ... }` + `let n = Node(key: key, ...)` with `consume key` params crashes both engines. R5/6.3 (retain-walk) territory | flow rule-B / `'heap` init lowering |
| B10 | A body whose tail is a branch join reaches `Terminator::Return` with ScopeExit DropCandidates unclaimed (no ReturnValue statement to run `wrap_cont_with_following_drops`) — owned **parameters** on that shape silently leak (locals survive via StorageDead pairing). The drain fix is written but backed out: it unmasks S7 (double-frees `Dict.insert`'s consume params). Sequencing: land S7's rule-B buffer retain FIRST, then the drain. Documented at `src/lower/mir_lowering.rs:1434-1452` | `src/lower/mir_lowering.rs:1434-1452` |

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
approved.

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

**7.2 (M5) The flow engine's three passes take a `Pass` enum.**
Replace `report_errors`/`recording`/`annotate` ambient booleans with one
explicit `Pass::{Fixpoint, Record, Report}` parameter threaded through
`transfer_block`/`transfer_statement`, deleting the save/restore
choreography at `cfg.rs:43-87`. Mechanical; makes the mode contract
type-visible.

**7.3 (M6) ADR 0017 stage 4: `lower_embedded_body`.**
Bundle the statement-scoped builder fields (`loop_stack`,
`handler_stack`, per-statement temp vecs, and — after 4.1 — the
enclosing-temp linkage) into one context struct swapped wholesale at the
two embedded-body sites. Also scope `scope_stack` so a `return` inside a
trailing block stops minting early-exit candidates for the *enclosing
function's* locals (currently neutralized by classification, not
structure).

**7.4 (M3) One authority per type question.**
"Expression type" = the typed tree; "binder type" = `local_tys`. Make the
accessors enforce it and delete the `.or_else()` fallback chains over
`node_types` (`mir.rs:406,618,1113,1168,1221`, `moves.rs:383`,
`cfg.rs:581`). `node_types` shrinks to whatever genuinely has no tree home
— if that set is empty, it's deleted.

**7.5 (M4) One spelling per ownership predicate.**
Route `symbol_has_conformance`'s CheapClone check and
`symbol_is_borrowed` through `GradeView`; fold `loans.rs`'s
`stores_borrow` into a `grades.rs` walk. Document, in the `grades.rs`
header, that typing's declared-grade Copy and flow's structural
`is_copy` answer different questions (coercion legality vs move-on-use)
with one example — so nobody "unifies" them and silently changes
semantics. The pre-monomorphization needs-drop carve-out is the one
sanctioned dual; it moves into the flow README (8.1) as such.

**7.6 (R7) Perm hygiene.**
`instantiate()` substitutes perms into predicates alongside tys/effs/rows;
`ExportSanitizer::fold_perm` gets a debug assertion that it only ever sees
post-`final_ty` types (or is changed to resolve through the store). Both
latent-only; both one-liners plus a unit test each.

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
