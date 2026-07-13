# 0029 — Uniform reference-counting baseline; ownership analysis becomes diagnostics and elision

Status: rejected after implementation trial (2026-07-12; accepted and
attempted the same day)

## Post-mortem (2026-07-12)

The clean-cut implementation was built to 1435/1484 suite-green in one
session and then reverted, on two findings the proposal got wrong:

1. **The cost model was wrong by an order of magnitude.** "Refcount
   traffic is not the bottleneck" assumed retains are instructions. In
   λ_G, a retain is a CPS continuation frame executed by an interpreter:
   the naive schedule took the suite from ~8 seconds to 127–340 seconds
   (15–40×). An interim state that slow is not shippable, and the elision
   optimizer that would recover it is exactly the precision machinery the
   ADR claimed could wait.
2. **The migration cost concentrated in hand-balanced core.**
   `core/Array.tlk`, the for-loop machinery, and the `@_ir` idioms
   (`Memory.replace`'s take-then-restore) were written against the flow
   schedule's precision; rebalancing them is per-construct design work,
   not mechanical cleanup — the per-construct surface the ADR set out to
   delete reappeared as per-construct migration.

What the trial validated (worth keeping in mind if this is revisited):
the architecture converged — 118 → 49 failures via five structural root
fixes, and failure modes flipped from double-frees to leaks exactly as
designed. Three genuine pre-existing bugs were found: `ExprKind::Clone`
results never get a temp candidate (finding F-A's actual root), the
temp substituter carries `ownership` marks onto operand references, and
MIR `Call` statements embed their argument nodes twice. These should be
fixed within the flow model via the findings inventory.

The plausible future shape, if the trust-chain problem warrants another
attempt, is the hybrid rejected as "option 3" at the time: the single-
writer pass with the flow analyses consulted as day-one elisions and the
naive rule as a per-shape fallback — old-model performance, one
authority, degradation to leaks instead of corruption. It was not chosen
because the migration cost (point 2) applies to it equally.

---

## Context

The ownership-soundness campaign (docs/ownership-soundness-plan.md) landed
all eight tracks on 2026-07-12: six checker-accepted memory-safety holes
fixed, the ADR 0017 free-balance verifier on by default in test builds,
the shadow drop authority and ambient-boolean passes deleted, a
grammar-restricted fuzzer in CI. The same day, the fuzzer's first session
produced four new findings (F-A through F-D), including one — F-A, a
`clone()` temp in borrow position — that the balance verifier cannot see.
M8's observation held: every recent ownership bug is a *combination*
(closure × temp, borrowed receiver × method × loop, handler × consume).
The repair pipeline works; the bug supply does not dry up.

The reason is structural, and it is the same trust-chain finding ADR 0017
made, taken one level deeper. A survey of every retain/drop/clone/deinit
decision site (2026-07-12) found:

- **Memory safety depends on optimizer-grade precision.** Lowering's
  emission consumes the flow pass's hardest judgments — loans, provenance,
  last-use liveness, temp classification, tier-2 auto-clones — through
  roughly 24 special-case gates (`ret_is_borrow`, `region_constructor`,
  `consumed_temps`, borrowed-root replace rules, `is_deinit_self`,
  `initializing_self`, the four `ArgMode` markers, …). Any imprecision in
  any of them, on any path, is a double free or a leak in a user program.
- **Emission is scattered per-construct.** Even with classification
  centralized in `flow/cfg.rs::classify_candidate`, the *emission* of
  drops is hand-placed across ~11 lowering paths (bind, assign, discard,
  return, call temps, match scrutinees, arm binders, early exits, unwind
  entries, finalizers, embedded bodies). Each new language construct adds
  a row to this matrix; each ownership feature adds a column. The fuzzer
  mines the cross product.
- **A second authority survives on the acquire side.** The `'heap`
  ledger's *releases* at scope exit ride flow's drop candidates
  (`classify_candidate` filters on `needs_drop || contains_object`,
  `flow/cfg.rs:584`), but the *acquires* and the rvalue-release rules
  (heap-regions plan rules A–E) are re-derived inside lowering from
  `rhs_is_rvalue` + `contains_object`, hand-placed across eight
  `mir_lowering.rs`/`calls.rs`/`matches.rs` sites with no per-point flow
  annotation — the shadow-authority pattern Track 7 deleted from the
  value-drop lane, surviving in the object lane.

The safety-critical surface is therefore all of `src/flow/` plus all of
`src/lower/` — ≈18k lines of non-test code — and there is no
trivially-correct baseline underneath it. Contrast the two systems this codebase already cites as
precedent:

- **Rust**: the borrow checker is diagnostics-only. Deleting borrowck
  changes which programs are *rejected*, never how an accepted program
  *behaves*; codegen correctness rests on one simple pass (drop
  elaboration over initialized-places dataflow). A borrowck bug is a
  wrong diagnostic, not a miscompile.
- **Swift**: the baseline is naive ARC — SILGen emits retains and
  releases mechanically, and a separate optimizer removes pairs only
  when it has a proof. A missed optimization is slow code, never a crash.

Talk fused the two: the checker's precision is load-bearing for memory
safety. That fusion is the one decision generating all the instances.

## Decision

Invert the baseline. Memory-management emission becomes a single, naive,
trivially-auditable elaboration pass; the flow pass becomes
diagnostics-only; precision returns later as an optional elision
optimizer whose failures cost performance, not safety.

The invariant this ADR exists to establish, stated as a test:
**disabling the flow pass may change which programs are rejected, but
must never change the behavior of an accepted program.** Today, deleting
flow breaks codegen. After this ADR, the code that cannot be wrong is
the one elaboration pass — small enough that total correctness of it is
achievable and machine-checked (the balance verifier proves its output
per lowered body).

### 1. One elaboration pass owns all retain/release emission

A single post-MIR pass emits the naive schedule:

- **retain** on every duplicating use of a droppable value: copy into a
  binding, a field, an aggregate, a closure capture, or an owned-mode
  argument;
- **release** at every scope exit, overwrite, and temporary end;
- **early exits and unwind entries release everything still
  initialized** — no liveness selection, no per-construct drainage
  choreography.

Its only inputs are MIR structure, an initialized-ness dataflow (the
existing `Static`/`Dead`/`Conditional`/`Open` shape, with drop flags for
the conditional cases — rustc's drop-elaboration design), and
`GradeView`'s `needs_drop`/`is_copy`. It reads no loans, no liveness, no
provenance, no flow annotations. `StatementOwnership` and
`flow/mir_annotate.rs` are deleted; lowering reads nothing from flow.

### 2. Borrows erase to +1 references at runtime; parameter modes stay +0

- A first-class borrow binding (`let x = &y`, match binders over
  borrowed scrutinees, loop binders) retains at bind and releases at
  scope exit. A checker hole involving borrows can then never dangle or
  double-free; the worst case is a redundant refcount bump.
- Borrow-mode *parameters* (ADR 0018's default) use the guaranteed +0
  convention **only where it is sound by structure alone**: when the
  argument is a place read rooted in an immutable local binding with no
  object dereference along the path. Such a place cannot be overwritten
  during the call — assignment in Talk targets celled (mutable) bindings
  and object fields, and an immutable root has neither — and its release
  sits at the caller's scope exit, after the call returns, on every path
  including aborts (the caller's unwind entry runs only after the callee
  frame is dead). No checker input needed.
- Every other borrow argument — a mutable (celled) root, an object-field
  path, a temporary — retains at baseline. The naive schedule releases
  on overwrite, so a callee-reachable overwrite of the borrowed place
  (a captured alias, reentrancy through effects) would otherwise free
  the value under a live +0 borrow *if the exclusivity checker has a
  hole* — and depending on exclusivity being hole-free is exactly the
  trust chain this ADR exists to break. Swift is the precedent that
  static exclusivity alone is not enough: SE-0176 mandates *runtime*
  exclusivity checks precisely for the shapes static analysis can't
  cover (escaping closures, class properties, globals). Widening +0 to
  these arguments later is an elision backed by the exclusivity
  analysis, or comes with Swift-style dynamic exclusivity checks —
  either way it exits the baseline.

This is Swift's `@guaranteed` convention composed with a language that
*does* have first-class borrow types — see Novel departures.

### 3. The region ledger folds into the same pass

`'heap` acquire/release become the object flavor of retain/release,
emitted by the same elaboration pass from the same initialized-ness
facts. The `rhs_is_rvalue` + `contains_object` re-derivation scattered
across `mir_lowering.rs`/`calls.rs`/`matches.rs` is deleted. One scheme,
one authority, for both value drops and object lifetimes.

The pass must preserve the ledger's **counted/uncounted distinction**,
because it is the cycle design (see Consequences): a handle copied into
counted storage — a binding, a value aggregate, an argument, a capture —
emits `RegionAcquire`; a handle stored into an *object field* emits no
count, because the runtime merges the two regions instead
(`talk-runtime/src/objects.rs::set_field` → `union`). The distinction is
structural (is the store target an object field or not), decidable from
the MIR statement alone with no analysis — so it lives in the
trivially-correct baseline, not in an optimizer.

### 4. Flow becomes diagnostics-only

Flow keeps exactly the judgments that are language semantics:
use-after-consume/move, exclusivity and aliasing, linearity
(`LinearNotConsumed`), borrow escape. It loses everything that existed
to feed codegen: `auto_clones` as a correctness mechanism (the baseline
retains anyway), temp classification, `consumed_temps`, the emission
gates. `moves.rs`/`loans.rs` shrink to their error-reporting cores, and
their spec collapses from "match the language rules AND produce a
balanced drop schedule" to "match the language rules" — testable
directly against an accept/reject corpus without running programs.

`consume` keeps its meaning entirely as a checker rule (the second use
is an error) and, later, as an elision hint. `'linear` remains
checker-enforced; accepted programs never duplicate a linear value, so
uniform RC on a uniquely-held value behaves as a move.

### 5. Elision is a separate, later optimizer with proof obligations

Last-use moves, consume-param forwarding, uniqueness-based in-place
mutation, and Perceus-style reuse return one transformation at a time,
each with an explicit proof obligation and each independently safe to
get wrong (the pair it fails to remove just runs). Every elision must
preserve the balance verifier's verdict and must not observably reorder
`Deinit` hooks relative to the baseline's scope-exit schedule.

### 6. The verifier and fuzzer stay, and their job gets easier

The balance verifier's role flips from "catch unsoundness in a 22k-line
surface" to "prove the one pass's output and catch elision regressions";
it runs with elision on and off. The fuzzer's oracle for the checker
becomes accept/reject conformance rather than memory corruption. The
two escape hatches on the verifier (`Driver::expects_leak`,
`TALK_SKIP_VERIFY_BALANCE`) are targeted for deletion — a baseline with
no per-construct cases should have no sanctioned exemptions.

## What gets deleted

All negative diff, inventoried from the 2026-07-12 decision-site survey:

- `flow/mir_annotate.rs` and `StatementOwnership` (the flow→lowering
  annotation channel), and `lower_candidate_drop_then`'s dispatch over it
- the per-construct drop drainage: `wrap_cont_with_following_drops`,
  `following_drop_candidates`, `unclaimed_scope_exit_drops`, the
  early-exit and `Terminator::Return` drains, per-statement temp vecs as
  a correctness mechanism
- liveness-selected unwind entries: ADR 0027's entries remain, but the
  one pass attaches an entry at *every* may-suspend MIR call site (the
  conservative `Unwind` candidates MIR already mints — which per the
  soundness plan already cover the value-call sites R9/F-B leak
  through; only the per-path lowering attachment was missing) and their
  content becomes "release everything initialized" — closing R9/F-B by
  making attachment uniform rather than per-call-shape
- the region-ledger re-derivation at its eight sites
- `auto_clones`/tier-2 clone emission, `ret_is_borrow`,
  `region_constructor`, `consumed_temps`, borrowed-root replace-to-Dead,
  and the rest of the emission-feeding gate family
- `expects_leak` and `TALK_SKIP_VERIFY_BALANCE`

What does **not** change: the language surface, the accepted/rejected
program set (the checker is untouched in the migration's first phases),
the "lowering emits, runtime executes" split (no runtime drop tables —
ADR 0027's rejection of a second runtime authority stands), and the
two-engine differential suite.

## Findings resolved by construction

F-A and F-C (temp/perform-arg leaks: temps release like everything else
initialized), the S7 class (constructor-arg retains: every duplicating
use retains, no marker gates), B8/B9 residue (pattern occurrences and
projection temps: no per-shape cases to miss), B10 (unclaimed
scope-exit drops: the pass has no "claiming"), R5/R6 (walk asymmetries:
one walk), R9/F-B (value-call unwind: entries release all initialized),
and the remaining B1 shapes. Each becomes at worst a missed *elision*
later.

## Consequences and risks

- **Refcount traffic increases at baseline.** Accepted: Talk's engines
  (tree-walking evaluator + VM) are not RC-bound, and elision restores
  performance incrementally with each step independently verified.
- **CoW uniqueness interacts with +1 borrows.** `Array`'s CoW gate is
  refcount-based (`_is_unique(self.storage.base)`, `core/Array.tlk`), so
  a live +1 borrow makes it see a shared buffer and copy where today it
  mutates in place. Correctness is unaffected (the copy is always safe),
  but two things bound the cost: borrow arguments rooted in immutable
  bindings — the common read path — stay +0 (decision 2), and `mut`
  receivers must stay count-neutral via inout transfer semantics
  (move-in/write-back, ADR 0018's v1 single slot), not via a counted
  borrow — otherwise every `mut` method on a container copies its
  buffer. Local-borrow elision is first in line after that. Swift's
  guaranteed convention exists for exactly this reason.
- **Deinit timing pins to scope structure.** The baseline releases at
  scope exit, and elision is obligated not to observably reorder hooks.
  Today's last-use moves can free earlier; if any test pins early
  freeing, that is a semantics decision to surface, not silently change.
- **Cycles are handled by the region design, and this ADR must not
  regress it.** Talk's answer to cycles is already built and tested:
  object-to-object references are *uncounted* — storing a handle into an
  object field merges the two regions (union-find; counts sum) — so a
  cycle inside a region holds no count on itself, and the whole region,
  cycles included, is finalized and bulk-freed when its *external*
  owner count reaches zero (`objects.rs` has the `a.next = b; b.prev = a`
  cycle test). Every channel that could smuggle a *counted* internal
  reference is a checker ban today: `EscapingObjectCapture`
  (`flow/captures.rs:146`), `ObjectInExistential`, `ObjectInRawStorage`.
  Under this ADR those bans stay as diagnostics, and the failure mode of
  a hole in them *improves*: the baseline retains captures like
  everything else, so a ban hole produces a balanced-but-immortal region
  (a self-referential count — a leak the live-object fences already
  detect), never a dangling handle. If those bans are ever relaxed —
  closures stored in object fields is the realistic ask — the options,
  each with prior art, are: allocate the capturing closure's environment
  into the captured region (merge semantics extend to it); a
  trial-deletion cycle collector scoped to region handles (Nim ORC's
  design — ARC everywhere, cycle collection only for types the compiler
  can't prove acyclic); or Swift-style `weak` annotations. That is its
  own ADR; what is decided *here* is only that internal-store-merges,
  external-handles-count is a baseline invariant the one pass preserves
  structurally.

## Alternatives considered

- **Keep hardening the current design** (verifier + fuzzer + fix
  findings). Rejected on the evidence of 2026-07-11/12: an eight-track
  repair campaign followed within a day by four new holes, one invisible
  to the verifier. Precision-everywhere has an unbounded combination
  space; the strategy does not converge.
- **Second-class borrows** (borrows as parameter conventions only; no
  stored/returned `&T`) — the Hylo/Mojo/Swift-`borrowing` shape. This
  deletes most of what makes the *checker* hard (provenance, loan joins,
  borrowed roots) and remains attractive, but it changes what programs
  are expressible (ADR 0021's `&Element` iteration, reference-returning
  lookups) and so is a language-identity decision. Deferred to its own
  ADR; this ADR is compiler-internal, makes that decision non-urgent,
  and composes with it either way.
- **Tracing GC.** Rejected: abandons deterministic `Deinit`, the region
  ledger, and the linearity story.
- **Runtime drop tables** interpreted by the VM at unwind time. Already
  rejected by ADR 0027 (second drop authority in the runtime); this ADR
  keeps that rejection.

## Novel departures

Flagged per the research-backed-plans convention; neither has direct
prior art as a composition:

1. **First-class borrow types erased to +1 at runtime.** Swift's ARC has
   no general first-class borrow types (its recent nonescapable
   `Span`-style types are narrow, checker-guaranteed views); Rust has
   the types but erases them to raw pointers, relying on borrowck for
   safety. Talk keeps the types in the checker (diagnostics,
   exclusivity) while making their runtime representation safe
   regardless of checker precision.
2. **Baseline-then-elide over a language with `consume` and `'linear`.**
   Perceus is precise-by-construction over a small core calculus; Swift
   has no linearity. Here linearity stays a checker-enforced property
   with no runtime obligation, layered over the ARC-style baseline.

## Staging

1. Build the elaboration pass behind a flag alongside current emission;
   the balance verifier and the full two-engine suite run both schedules
   and compare observable behavior. TDD: the F-A/F-C repros and the
   fuzzer's `DEFAULT_SKIPS` entries become the pass's first green tests.
2. Flip the default (cfg(test) first, then everywhere); delete the
   per-construct emission paths and gates; unskip the fuzzer findings.
3. Delete `mir_annotate.rs`; shrink flow to diagnostics; add the
   invariant test — a full-suite run with flow's analysis disabled must
   produce identical program behavior (only diagnostics disappear).
4. Elision oracle as a separate opt-in pass, one transformation at a
   time, verifier-gated.

Lines removed vs added tracked per stage; stages 2–3 must be strongly
negative.

## Citations

Per-decision prior art, verified 2026-07-12 (entries marked * were
verified 2026-07-11 for docs/ownership-soundness-plan.md and are reused):

- **Decision 1 (naive schedule + separate optimizer)**: Swift's compiler
  pipeline — SILGen emits reference-counting operations mechanically;
  the SIL optimizer's ARC pass removes redundant pairs.
  [Swift.org: Swift Compiler](https://www.swift.org/documentation/swift-compiler/),
  [swift/docs/OptimizerDesign.md](https://github.com/swiftlang/swift/blob/main/docs/OptimizerDesign.md),
  [ARC Optimization for Swift](https://apple-swift.readthedocs.io/en/latest/ARCOptimization.html).
- **Decision 1 (initialized-ness dataflow + drop flags)**: rustc's drop
  elaboration.*
  [rustc-dev-guide: drop elaboration](https://rustc-dev-guide.rust-lang.org/mir/drop-elaboration.html).
- **Decision 2 (+0 guaranteed convention)**: SIL's `@guaranteed`
  parameters — caller guarantees validity for the call's duration, so
  callee retain/release pairs are eliminable.
  [SIL documentation](https://apple-swift.readthedocs.io/en/latest/SIL.html),
  [Swift ownership/ARC roadmap](https://forums.swift.org/t/a-roadmap-for-improving-swift-performance-predictability-arc-improvements-and-ownership-control/54206).
- **Decision 2 (static exclusivity alone is insufficient for +0 on
  mutable places)**: SE-0176 — Swift requires *dynamic* exclusivity
  enforcement for the shapes static analysis cannot cover (escaping
  closures, class properties, globals), on by default since Swift 5.
  [SE-0176: Enforce Exclusive Access to Memory](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0176-enforce-exclusive-access-to-memory.md),
  [Swift 5 Exclusivity Enforcement](https://www.swift.org/blog/swift-5-exclusivity/).
- **Decision 4 (checker as pure diagnostics)**: NLL/borrowck computes
  facts for error reporting; codegen does not consume them.*
  [RFC 2094 (NLL)](https://rust-lang.github.io/rfcs/2094-nll.html),
  [rustc-dev-guide: the borrow checker](https://rustc-dev-guide.rust-lang.org/borrow-check.html).
- **Decision 5 (elision target)**: Perceus precise reference counting —
  the garbage-free theorem is the elided endpoint's spec.*
  [Reinking, Xie, de Moura, Leijen — Perceus (PLDI '21)](https://dl.acm.org/doi/10.1145/3453483.3454032).
- **Decision 3 / cycles (region rc, uncounted internal references)**:
  the ledger's own design citation (Gay–Aiken region reference counting,
  per docs' heap-regions plan); the cycle-collector fallback named for
  the relaxation scenario is Nim ORC — ARC plus trial-deletion cycle
  collection, invoked only for types not provably acyclic.
  [Nim blog: ORC — Vorsprung durch Algorithmen](https://nim-lang.org/blog/2020/12/08/introducing-orc.html),
  [Nim memory management](https://nim-lang.org/docs/mm.html).
- **Alternative (second-class borrows)**: Hylo's four parameter
  conventions (`let`/`inout`/`sink`/`set`) over mutable value semantics,
  with no first-class references.
  [Hylo language tour: functions and methods](https://docs.hylo-lang.org/language-tour/functions-and-methods),
  [hylo-lang.org](https://hylo-lang.org/).

## Open questions

1. **Baseline deinit timing** — pin scope-exit as the language's
   observable semantics (recommended: predictable, matches declaration
   structure), or preserve today's earlier last-use frees as pinned
   behavior elision must reproduce?
2. **`mut`/inout is a transfer, not a borrow — pin its baseline
   accounting.** The count-neutral move-in/write-back reading (the slot
   is uninitialized for the call's duration; the callee owns the value)
   is what keeps `mut` container methods from copying (see the CoW
   consequence), but it needs two things nailed down before stage 2: a
   test that uniqueness checks inside a `mut` method see count 1, and a
   decision on what a mid-call aliased write to the same celled slot
   means (Swift answers this with SE-0176's dynamic exclusivity checks;
   Talk needs either the same or a structural argument that no alias to
   a celled slot can exist during the call).
3. **Existential and witness-dispatched retains** (the
   `retain_payload`/drop-witness slot pairing): the structural walk in
   `statements.rs` survives as the *implementation* of retain/release on
   composite values — confirm it stays symmetric when driven from one
   pass (it should, that is 6.3's landed invariant).
