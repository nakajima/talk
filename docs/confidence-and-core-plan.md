# Confidence and Core: hardening the pipeline instead of rewriting it

Status: proposed (2026-07-02)

## Context

A 16-line real program (`runner.tlk`) surfaced four defects this week: a
`for`-desugar hole (body block arguments bound a second, never-reseeded
symbol), a match-through-borrow typing failure (scrutinee types still
unresolved at generation time got pinned to the owned enum), a runtime double
free (borrowed-match payload binders dropped values their owner still held),
and — found while testing the fix — **containers never deep-drop their
elements**: every `Array`/`Dict` of droppable values has always leaked its
contents' heap buffers. All four reproduce on `main`; none were introduced by
the flow-on-CFG branch. The first three are fixed on the branch, with tests
that fail on `main`.

The finding that matters is not any one bug: it is that the suite was green
the whole time. Allocation balance is asserted in roughly a dozen
`run_heap_eval` tests; the other ~970 check values and stdout. And no test in
the corpus had ever run the language's most idiomatic composition —
iterate a collection and match each element — end to end. Green does not
currently witness memory correctness, and the pipeline's middle end
(HIR → MIR-with-embedded-HIR → λ_G) re-implements the full ~20-construct
surface language per stage, which is where rough edges keep being minted
(see the construct-width analysis in the core-IR review of 2026-06-30).

## Decision shape: what "start over" should and shouldn't mean

Rebuilding "everything after name resolution" would discard the two most
mature, least-implicated subsystems — the type solver (HM + rows + effects +
protocols/GADTs) and the backend (λ_G, evaluator, VM, CoW runtime), which
disagreed with each other zero times all session — to punish the layer
between them. The classic rewrite failure mode is re-deriving working
decisions during a long dark period with no working compiler
(the strangler-fig migration exists as the antidote). The evidence points
at (1) the coverage regime and (2) the middle end's width. Both have
incremental fixes:

- **Track A** makes green mean something (allocation balance by default, a
  real-program corpus).
- **Track B** closes the one known memory hole (container element teardown).
- **Track C** is the scoped version of "start over after name resolution":
  elaborate to a ~11-form Core IR early, so typing/flow/lowering stop each
  owning the whole language. The flow engine and MIR store built by ADR 0010
  sit downstream of where Core lands and carry over.

Nothing in Track C is speculative — it is the existing core-IR elaboration
plan (2026-06-30), whose phases 1–2 were already proven green in the
`worktree-desugar-phase` worktree.

## Track A — make green trustworthy

**A1. Allocation balance is the default assertion, not opt-in.**
Extend the vm test harness so every program-running test executes on the
allocation-tracking evaluator and asserts `live_allocations` (and
`live_objects`) balance to zero at exit. Precedent: CPython's refleak
buildbots run the whole suite under `regrtest -R`, which fails any test that
leaks references or memory blocks — leak detection as suite policy, not
per-test heroics. The first sweep will fail every container-holding test;
each failure becomes either a fix or an explicit, greppable
`expects_container_element_leak()` marker on the assertion (not `#[ignore]`,
not a TODO — a first-class enumeration of the known deficit). Track B's exit
criterion is that this marker's use count reaches zero and the marker is
deleted. VM-side allocation accounting doesn't exist today; the VM keeps its
value/stdout parity role (candidate follow-up, not in scope).

**A2. A real-program corpus.**
`tests/programs/*.tlk`: small, idiomatic, complete programs (the runner.tlk
shape; iterate-and-match; string building; dict usage; handlers; the
repro programs from this week's fixes), each checked and run on both engines
under A1's accounting. This is differential testing in the McKeeman sense —
two implementations, same inputs, any divergence is a bug — which the
eval≡VM fixture suite already practices; the corpus extends it from
constructed fixtures to whole programs. Grammar paper-cuts get corpus
entries as they're fixed (`if i == n {` struct-literal ambiguity, bare
`continue` before `}`, `let x = { … }` record/block ambiguity) so the parser
decisions are pinned.

**A3. Land the branch in reviewable pieces.**
Proposed partition, each of which was a verified-green checkpoint during the
work: (1) control-flow-complete MIR scaffolding + builder
statement-ification; (2) pre-flow MIR store + structural candidates;
(3) the CFG flow engine; (4) scaffold-based lowering + candidate-driven
early exits; (5) single annotation home; (6) the iteration/match sweep
(desugar fix, `PatternView`, borrowed-match aliasing). Commits are yours;
`/code-review ultra` on the result is a cheap independent pass before merge.

Exit criteria for Track A: suite green under default allocation assertions
(with the fenced container markers as the only exceptions), corpus running
in CI, branch landed.

## Track B — container element teardown

The gap: `lower_drop_value_then` drops raw-storage-backed structs by
`Free(ptr)` on the RawPtr field; elements in the buffer are never torn down.
Eager element drops are wrong under CoW — Array buffers are shared, and the
write barrier already encodes uniqueness — so teardown belongs at **last
release of the refcounted storage**, with a per-element-type finalizer.
This is the standard shape: Swift's arrays are refcounted
`ContiguousArrayStorage` whose deinit destroys elements at last release;
Lean 4 (Counting Immutable Beans) and Koka (Perceus) build the whole runtime
on RC with destructive teardown at refcount-zero, using RC-uniqueness for
in-place updates exactly like our write barrier. We already synthesize
per-instantiation finalizer thunks for `'heap` regions — the element
finalizer reuses that machinery.

Steps:
- **B0 (investigate first):** characterize the existing buffer lifecycle.
  `CheapClone` is documented as "an O(1) buffer retain", which implies some
  refcount already exists on ByteStorage-backed buffers. If so, the fix may
  be an element-release loop in the existing last-release path rather than a
  new header. Do not design past this step until it's answered.
- **B1:** refcount-aware storage release with element finalizer thunk
  (design per B0's findings); Array first, then Dict (same storage
  machinery), then String's ByteStorage if B0 shows it's not already
  covered.
- **B2:** flip A1's leak markers off container by container; delete the
  marker.

Flow-checker note: no checker change expected — array drops are already
scheduled and classified; only the value-drop lowering deepens. The checker
already refuses `'heap` handles in raw storage (`ObjectInRawStorage`) for
scan-blindness; owned elements were the silent half of that same blindness.

## Track C — Core IR elaboration (the structural fix)

Target and phasing are the 2026-06-30 plan, restated: elaborate after typing
to a small ANF core (~11 forms: atoms, app, lam, let/letrec join points,
con/proj, case, record, perform/handle, pack), so branching collapses to
`case`, statement control flow to join points, aggregates to `con`, and
witnesses to ordinary atoms. MIR then carries Core operands instead of
embedded HIR expressions — which retires this branch's two accepted
residuals by construction (the unannotated fallback for inlined constants,
and the drop-stack remainder), and ends the scaffold-blocks-plus-
embedded-copies duality that made ADR 0010 hard. Prior art: GHC's tiny Core
under a rich surface (System FC), Rust's THIR/MIR split, join points
(Maurer et al., PLDI 2017), ANF (Flanagan et al., PLDI 1993).

Phases (each gated by the eval≡VM suite, now strengthened by Track A):
1. Desugar-phase extraction (proven in `worktree-desugar-phase`; redo on
   this branch — the worktree predates ADR 0010 and deleted
   `hir::ExprKind::If`, which this branch's scaffolding still uses, so it's
   a reference implementation, not a merge source).
2. Type-independent collapses, one construct per commit (expr-`if`→`case`
   first; the worktree's eager-join match-typing fix comes along).
3. `build_core` with type-directed elaboration (pack, witness atoms,
   coercion erasure); re-point flow + lowering.
4. Statement control flow → join points (this subsumes the builder's
   `tail_exits`/`TailReturn`/scaffold special cases — they become ordinary
   `case` + join lowering).
5. MIR statements carry Core operands, kind by kind.
6. Decompose `lower/` into ordered narrow passes (match-compile, monomorph,
   closure-conv, CPS).

Track C starts only after Track A exits: migrating representations without
the leak-checking corpus is how the current blind spots were minted.

## Ordering

**Revised 2026-07-02 (Pat's call): C runs first.** The simplified middle
end is the priority; hardening lands on the simplified pipeline instead of
the wide one. New order: C1…C6 → A1 → A2 → A3 (land) → B0/B1/B2. The
accepted risk is the one the original ordering existed to avoid — C's
join-points phase (C4) can silently shift drop timing without the default
allocation assertions watching. Mitigation: the existing explicit
`run_heap_eval` balance tests gate every C phase, and each construct
collapse adds a balance test for the construct it touches, so the
assertion coverage grows along the same path C walks. The corollary
stands and is now trivially satisfied: language-semantics defects found
during C get fixed in the collapsed form, not patched per-construct.
Rough sizing: C is the long arc but every phase leaves a working
compiler; A is days; B is B0-dependent but bounded.

## Citations (per decision)

- **Leak-checking as suite policy (A1):** CPython's `regrtest -R`
  refleak hunting and Refleaks buildbots —
  [refleak.py](https://github.com/python/cpython/blob/main/Lib/test/libregrtest/refleak.py),
  [handle-leak extension](https://github.com/python/cpython/pull/7827).
- **Differential testing (A2):** W. M. McKeeman, "Differential Testing for
  Software", Digital Technical Journal 10(1), 1998 —
  [paper](https://www.semanticscholar.org/paper/Differential-Testing-for-Software-McKeeman/fc881e8d0432ea8e4dd5fda4979243cac5e4b9e3);
  the eval≡VM fixture suite is already this pattern, the corpus widens its input space.
- **Element teardown at last release of refcounted CoW storage (B):**
  Swift's `ContiguousArrayStorage` (refcounted class storage; elements
  destroyed in deinit; CoW via uniqueness check) —
  [ContiguousArray.swift](https://github.com/apple/swift/blob/master/stdlib/public/core/ContiguousArray.swift),
  [Array docs](https://developer.apple.com/documentation/Swift/array);
  S. Ullrich & L. de Moura, "Counting Immutable Beans: Reference Counting
  Optimized for Purely Functional Programming", IFL 2019 —
  [paper](https://arxiv.org/abs/1908.05647),
  [Lean RC docs](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/);
  Reinking, Xie, de Moura, Leijen, "Perceus: Garbage-Free Reference Counting
  with Reuse", PLDI 2021 (Koka).
- **Small core under a rich surface (C):** GHC Core / System FC (Sulzmann,
  Chakravarty, Peyton Jones, Donnelly, TLDI 2007); Rust's THIR/MIR split
  ([RFC 1211](https://rust-lang.github.io/rfcs/1211-mir.html), already the
  basis of ADR 0010); join points (Maurer, Downen, Ariola, Peyton Jones,
  "Compiling without Continuations", PLDI 2017); ANF (Flanagan, Sabry,
  Duba, Felleisen, "The Essence of Compiling with Continuations",
  PLDI 1993).
- **Migration over rewrite:** strangler-fig incremental replacement
  (Fowler); every phase above leaves the compiler working, which a
  post-name-resolution rewrite cannot.

**Novel departures, flagged:** the `expects_container_element_leak` marker
(A1) — fencing a known deficit inside the assertion rather than skipping
tests — is our own convention (CPython's analog is suppression lists, which
hide rather than count); and running flow on MIR that carries whole
expression trees (ADR 0010's "no three-address flattening") remains a
departure from rustc that Track C phase 5 retires.

## Risks

- A1's first sweep may surface leaks beyond containers; that is the point,
  but it makes A's size estimate soft. Each finding gets the fence-or-fix
  treatment, never suppression.
- B before B0 is unknowable; if B0 reveals no existing refcount, B grows a
  runtime header change (still bounded, but touches the VM and evaluator).
- C phase 4 (statement control flow → join points) is the riskiest collapse
  — it's where `if`-divergence typing and flow's CFG interact; it lands
  after the corpus exists for exactly that reason.
- The `worktree-desugar-phase` work must be treated as reference only;
  merging it would resurrect deleted-construct conflicts with this branch.
