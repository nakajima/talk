# Lean backend rebuild plan

Status: reset complete; waves 2, 3, 4, 5, 6, and 7 reopened against the
reference test audit — see
[True parity](#true-parity-2026-07-16-revision) for the gates and
[How the audit gaps slot into the plan](#how-the-audit-gaps-slot-into-the-plan-2026-07-17)
for why each wave reopened. Those sections govern.


Historical implementation baseline: `pre-backend-reset-2026-07-13` at
`96249e71`

Frontend-only implementation base: `a1d20d27`

Current experimental rewrite: `de06bd37`

Parity accounting: [Backend parity ledger](backend-parity-ledger.md)

Frozen observable outputs: `tests/parity/programs/*.stdout`

## True parity (2026-07-16 revision)

The original plan defined "parity" through artifacts this repo authors:
the capability ledger and 16 frozen corpus programs. Executing against
real programs falsified that definition — roughly twenty-five defects
(several memory-unsafe miscompiles among them) lived in the gap between
"ledger rows closed" and "runs the programs the released compiler ran."
The proxy was satisfiable while the target was not (Goodhart's law); for
calibration, differential testing has found hundreds of latent defects
in mature production compilers (Yang et al., PLDI 2011 — Csmith vs
GCC/LLVM), so the defect count was a normal first-contact curve. The
failure was measuring readiness against a proxy and claiming done there.

**Parity claims are counts against the gates below. Nothing else counts
as a parity statement.**

### Acceptance gates

| Gate | What runs | How it runs | State (2026-07-17) |
| --- | --- | --- | --- |
| G1 | `core/*.test.tlk` via real `talk test` | CI: `talk_test_runs_the_core_suites` | GREEN (18 tests) |
| G2 | `tests/programs/*.tlk` vs frozen stdout | CI: parity tests | GREEN (16 programs) |
| G3 | External Talk projects' full `talk test` suites | CI opt-in: `talk_test_runs_acceptance_projects` over `TALK_ACCEPTANCE_DIRS` (colon-separated project roots) | talk-syntax 224/224 GREEN (2026-07-17); talk-html GREEN |
| G4 | Embedding surfaces | CI: REPL tests, talk-c unit tests, Swift XCTest (`talk-swift`, needs a Swift toolchain) | GREEN |
| G5 | Vendored reference examples (`tests/examples/`) vs frozen stdout | CI: `examples_corpus_matches_frozen_stdout` | 16/16 pinned GREEN; burn-down list empty (2026-07-17) |
| G6 | Reference VM behavior pins (~180 portable of 220) | CI: `reference_*_cluster_matches_frozen_stdout` corpus tests | 4 clusters GREEN (effects 18, strings 11, collections 35, drops 15) — 79 pins |

Known additional corpus on this machine: `~/apps/talk-syntax`,
`~/apps/talk-html`, `~/apps/talktalk.sh/test.tlk` (runs). Blocked on
frontend/stdlib drift rather than the backend: `~/apps/talispk` (uses
`reduce`, absent from current core), `~/apps/talk-test` (its
`package.tlk` is source, not a manifest — package detection collides).

### Burn-down: the 16 open G3 failures, by root cause family

**All sixteen closed 2026-07-17.** The five symptom families reduced
to three backend ownership bugs plus one leak already fixed in wave 5:

| Symptom family | Actual root cause |
| --- | --- |
| F1, F3, F5 | Constructions consumed arguments with bare `consume_operand`: a field read passed to a construction moved the buffer out from under its owner (Borrowed-classified view types exempt — they never own what they look into) |
| F2 | Match-arm bindings lived in the statement-temp list, so any inner statement boundary dropped them mid-arm (drop-then-retain double frees); and the return path's temp flush consumed shared ownership state, corrupting sibling arms (the residual leaks) |
| F4 | `return` never flushed statement temporaries — chained-concat intermediates leaked (fixed during wave 5) |

Diagnosis tooling: `TALK_TRACE_MEM` (alloc/retain/free with chunk+pc
sites, alloc-site lines, trap-site disassembly),
`TALK_TRACE_MEM_PTR=<addr>` (per-pointer disassembly windows),
`TALK_DUMP_MIR` (composed-suite MIR), `TALK_BACKEND_DEBUG`
(demand/instance/dispatch traces).

### Coverage the gates still lack (admitted, not hidden)

- Effects: no external program exercises user effects beyond the test
  harness's `'fail`/`'registerTest`. Generic-effect witness passing is
  covered only by this repo's own black-box tests.
- Packages with remote dependencies: only the offline/starter path runs.
- The wasm surface shares the talk-c program path but has no
  runtime-level gate of its own.
- Derived `Showable`/`Equatable` are exercised externally only where
  talk-syntax happens to compare enums.

### The reference column (audited 2026-07-17)

"True parity" needs a reference compiler. The audit found that **none
is reconstructible** — every candidate state fails to run the external
corpus it supposedly defined:

| Candidate | State | Result on pristine talk-syntax |
| --- | --- | --- |
| `pre-backend-reset-2026-07-13` (96249e71) | last pre-reset tree | internal panic: "checked MIR both transfers and releases runtime obligation" |
| 0.1.50 bump (3226cceb) | last version bump | internally inconsistent: its own core uses `take` inline IR its own parser rejects; cannot run its own suite |
| `~/apps/talk` HEAD (`lean-backend`) | the sibling repo's own rebuild | no `test` subcommand yet |
| installed `talk` binary | stale build of the sibling repo | rejects `assertMessage` (embedded stdlib drift) |
| crates.io | never published (the `talk` crate is unrelated) | — |
| **this branch (bigdiff)** | at audit time (now 224/224) | **207/223 + all core suites + talk-html green** |

Consequences:

- The reference is the corpus itself: talk-syntax's committed test
  expectations (and every other real Talk program) define correct
  behavior. No compiler state outranks them.
- By count, this branch already runs more real Talk than any other
  available state of the compiler.
- `assertMessage` was the baseline stdlib name; the rebuild lineage
  renamed it to `assert_message`. The name is restored as an alias so
  existing programs run unmodified — baseline API names are part of
  parity.

### How the audit gaps slot into the plan (2026-07-17)

A full read of the mature compiler's test suites (`~/apps/talk` main,
0.1.62): 220 VM behavior tests, 219 flow/ownership rule tests, the
33-program `examples/` corpus (now vendored as gate G5), plus frontend
suites (ours is already a superset of those).

The audit did not find a missing execution wave. Every gap belongs to
a wave the plan already had — the waves were closed against the wrong
evidence. Three distinct failures produced the gaps:

1. **Dropped scope.** Wave 5's own text required cells ("captures,
   cells, recursive local functions"). Ledger row CHG-06 quietly
   narrowed that to "Copy and shared borrows only," and the narrowing
   won without anyone reviewing it against the plan. A ledger row may
   not narrow a wave's scope; scope changes are plan edits.
2. **Under-specification.** Wave 6 said "dynamic nearest-handler
   routing" and stopped. ADR 0011 departure (d) additionally requires
   function values to capture the capabilities of their creation site
   (effects as capabilities — Brachthäuser, Schuster & Ostermann,
   OOPSLA 2020), and no driving program distinguished the two rules.
3. **Proxy exits.** Wave 3 licensed "the minimum borrow checking
   required by real source behavior," where real source behavior meant
   16 self-authored programs. Silent acceptance of unsound programs is
   invisible to passing programs by construction; only the reference's
   rejection tests can see it.

Accordingly, gaps are not a separate backlog. Each is filed back into
its owning wave, and the reference suites become the exit criteria the
waves should have carried from the start:

| Gap | What it is | Owning wave | Exit evidence |
| --- | --- | --- | --- |
| S1 | Lexical capability capture: closure `f() + 'boost()` under two nested handlers must print 300 (creation-site handlers); dynamic handler search gives 400 | 6 (reopened) | reference effects cluster of G6 + the capture pin |
| S2 | FileIO/TrailingBlock stdout divergence; Identity/Show leaks | 7 / 5 (diagnose) | G5 known-failing list shrinks |
| F1 | Mutable captures (cells) + capture lists `[consuming s]` / `[&s]` / `[copy s]`; supersedes CHG-06 | 5 (reopened) | closure/cell cluster of G6; Capture and Counter examples |
| F2 | Record patterns (`match r { { x, y: 123 } -> … }`) and record destructuring (`let { x, y } = …`) | 2 (reopened) | StructuralTyping example; record-pattern pins |
| F3 | Inferred (unannotated) generic functions — `func fib(n)` fails at a conformance-dictionary boundary | 5 (reopened) | Fib example |
| F4 | Multi-file `talk run` traps on an arena handle | 7 (reopened) | Imports example off known-failing |
| F5 | Unique types (`*String`) | 3 (reopened) | unique-type flow rules |
| F6 | `for x in consume xs` / `for x in mut xs` exist but are unverified against the reference | 4 (reopened) | iteration-mode pins in G6 |
| C | 219 flow/ownership rules the deleted checker enforced (NLL-style liveness (RFC 2094), borrow provenance, partial moves with sibling tracking, loop-carried moves, capture modes, ADR 0018 markers); this backend accepts most silently | 3 owns the core; the capture-mode slice rides with wave 5 | ported accept/reject suite; any deliberate divergence argued in writing |
| V | ~180 architecture-independent VM behavior pins (strings/UTF-8, iterator adapters, full effects suite, heap/region semantics, drop-once/leak balances) | sliced per wave as G6 | each wave's cluster green before the wave closes |

**Wave-closure rule (new):** a wave is closed only when its reference
cluster is green, or every divergence in the cluster carries a written
argument. "Its driving programs pass" is no longer a closing condition.

### Deepen, don't sprawl (2026-07-17 review)

Every reopened wave lands where a mechanism already exists, so each is
a fork: extend the existing mechanism or grow a parallel one. The
review below binds each wave to the deepening choice (deep modules:
Ousterhout, *A Philosophy of Software Design*, 2018 — more
functionality behind the same interface, not more interfaces). These
are obligations, not suggestions; violating one is a stop condition
under the working model.

1. **One closure-environment contract (waves 5 and 6).** Closures
   already carry hidden captures next to explicit ones: witness pairs
   inherited through `sorted_witnesses()` and conformance
   dictionaries ride the environment today. Cells (wave 5) and
   capability slots (wave 6) are two more kinds of environment slot,
   not two new mechanisms. Wave 5's rework defines the single
   contract — explicit captures by mode, plus hidden captures
   (witnesses, dictionaries, capabilities) — with one layout rule and
   one retain/drop rule; wave 6 adds capability slots to that
   contract. A separate capability table or a second inheritance path
   is forbidden.
2. **Cells are boxes plus the existing place machinery (wave 5).**
   `write_place` already understands heap links (copy-on-write
   writeback stops at them); mutation through a captured cell is a
   `PlaceChain` with a heap link. Assignment conversion happens once
   during MIR construction — captured-mutable locals become box
   allocations, reads and writes become projections. No new VM
   opcode, no new IR operation, no cell runtime type distinct from
   the existing managed box.
3. **Inferred generics are the same schemes (wave 5).** The
   dictionary machinery (`witness_params`, demand-time witness
   recording, requirement closures) must not grow an
   unannotated-function path. If inferred schemes bypass witness
   recording somewhere, fix the one path; any code that can tell an
   inferred scheme from an annotated one is the defect.
4. **Record patterns reuse the tuple arm (wave 2).** The backend
   already lowers `PatternKind::Tuple` and records are tuple-layout.
   Resolving field names to positions is row typing and belongs to
   the checker; record patterns and `let { x, y }` reach the backend
   as name-resolved positional patterns. Target: zero new backend
   pattern machinery — at most a thin alias, never a second
   projection engine.
5. **One ownership checker, one place representation (wave 3).**
   Porting the 219 rules must not resurrect the deleted flow checker
   as a second semantic owner. The rules extend the existing MIR
   ownership analysis, and partial-move/sibling-field tracking uses
   the same `PlaceChain` the compiler uses for writebacks — not a
   second path lattice. Provenance messages are presentation over
   that one analysis (per the provenance policy). Unique types are a
   qualifier on the existing ownership modes, not a parallel type
   universe.
6. **One corpus runner (gates G2, G5, G6).** `tests/programs` and
   `tests/examples` already have separate frozen-stdout runners, and
   the ~180 G6 pins would naturally become a third. Merge into one
   directory-driven runner before porting the pins; pins that check
   values rather than stdout print and compare. This item deletes
   code net of what it adds.
7. **One source-graph loader (wave 7).** Whole-reachable-graph
   compilation exists on the package path (TOOL-08). If the Imports
   arena trap turns out to come from a second loading path for
   multi-file `talk run`, the fix is to make run the package path
   with a synthesized root and delete the divergence — not to patch
   the second path into agreement.

Wave 4 offers no deepening beyond item 6 — it is verification work by
construction. Reopened waves inherit the stop conditions of the
working model; where a wave replaces a special case (item 2 replaces
the capture-rejection diagnostics, item 7 may delete a loader), the
special case is deleted in the same wave.

### Rules going forward

1. Parity vocabulary is banned outside gate counts.
2. Every backend change runs G1/G2 (CI) and, when touching ownership,
   generics, dispatch, or effects, a G3 sweep before it merges.
3. When behavior is unclear, mine the archived implementation
   (`pre-lean-rebuild-2026-07-16`, and 0.1.50 at `3226cceb` for the
   evaluator) for the encoded semantics before re-deriving them — the
   deleted flow checker was the ownership spec, not bloat.
4. Every fail-closed rejection carries: a message naming the construct,
   a black-box test pinning it, and either a ledger row demanding it or
   a written soundness argument.
5. New capabilities land with external-corpus evidence when any exists,
   not only self-authored tests.

## Purpose

Restore the required behavior of the last green compiler through one reference
backend while ending with a compiler that is materially smaller, deeper, and
easier to understand than the archived implementation.

This plan replaces feature-first contract expansion with behavior-first
implementation. It preserves accepted language semantics, but it does not
preserve the current rewrite's module interfaces, artifact shapes, validators,
fixture frameworks, or integration ceremony merely because they exist.

The current rewrite is evidence and a source of tests. It is not the mandatory
foundation of the next implementation.

## Why another reset is justified

The frontend-only reset removed about 41,000 Rust lines. The current rewrite has
added about 34,000 back while restoring only a minority of backend behavior.
Since `a1d20d27`, the branch has accumulated roughly 48,000 added lines against
fewer than 5,000 deleted lines.

The cost is structural rather than isolated to one commit:

- the canonical TypedProgram copied a large portion of frontend meaning into a
  second representation;
- private internal seams received serialization-grade validators;
- future feature shapes and fixture systems landed before production behavior;
- each narrow capability paid repeated producer, validator, verifier, fixture,
  handshake, documentation, and adapter costs;
- parallel lanes froze shallow interfaces and encouraged additive modules;
- no merge gate measured production size, interface size, deletion, or
  duplicated semantic rules.

Continuing on that cost curve would make a later simplification harder and less
likely. The implementation should therefore reset before aggregates, closures,
effects, and managed storage cement the current interfaces.

## What success means

Feature parity and architectural success are both required.

### Behavioral success

- Every Required row in `docs/backend-parity-ledger.md` executes through the
  bytecode reference backend or produces the reviewed source diagnostic.
- All 16 programs in `tests/programs` match their reviewed output, cleanup, and
  resource behavior.
- `talk run`, package execution, source tests, REPL execution, standalone
  execution, C/Swift embedding, and browser embedding use the same compiler and
  runtime path.
- Required unsupported paths are gone. Deliberately deferred or unsafe behavior
  rejects explicitly.
- No evaluator, lambda-G authority, or compatibility backend returns.

### Architectural success

- The production backend, including frontend code added solely to feed it and
  runtime adapters added solely to execute it, is smaller than the corresponding
  archived production implementation. The reset checkpoint records the exact
  baseline and sets a reviewed full-parity budget; the target is at least 50%
  smaller, not merely one line below the archive.
- The compiler exposes one deep backend interface. Phase representations remain
  private implementation details.
- A semantic rule has one owner. It is not reconstructed or independently
  revalidated at every internal seam.
- No production module exists only to support hypothetical future behavior or
  test fixtures.
- Deleting a module would force its complexity into multiple callers. If
  deletion simply removes complexity, the module is too shallow to keep.
- Tests primarily exercise the same interface used by real source compilation.

Line count is a stop signal, not a substitute for design review. Blank lines,
comments, tests, generated code, and documentation are reported separately so
that production reductions cannot be manufactured by moving code between
categories.

## Decisions retained

The reset reopens implementation architecture, not source-language semantics.

### Frontend authority

- Parsing, name resolution, type inference, conformance selection, use modes,
  capture modes, effect rows, and diagnostics remain frontend responsibilities.
- Downstream compilation does not search conformances or reinterpret source
  syntax.
- Retained syntax trees provide syntax and ranges, not fallback semantic
  answers.
- Borrow-by-default parameters, sequential local scope, protocol argument
  identity, existential typing, and current operator semantics remain as
  already decided.

Relevant sources include ADRs 0001-0007, 0013-0016, 0018, 0020-0026, and the
existing type-system plans.

### Ownership and effects

- MIR is the one source-level CFG and owns moves, borrows, cleanup, pattern
  control flow, and ownership diagnostics.
- Copy, Move, Borrow, clone, witness, and handler choices come from typing.
- Borrowed values do not escape; ordinary loans do not cross suspension.
- Cleanup order, one-shot continuation behavior, Resume/Discontinue semantics,
  and dynamic deep-handler routing retain their accepted meanings.
- Successful editor explanations derive from MIR. Rejected programs carry the
  facts needed by their diagnostic; there is no persistent parallel provenance
  artifact.

Relevant sources include ADRs 0010, 0011, 0014, 0015, 0017-0019, 0021, 0025,
0027, 0028, and 0030, plus `docs/ownership-soundness-plan.md`.

### Runtime and storage

- Talk `Int` is signed 64-bit with the reviewed arithmetic and division
  behavior.
- `Character` remains a borrowed extended-grapheme view.
- Uniform reference counting remains rejected.
- Managed buffers, type-specific CoW, merge-only heap regions, lifecycle hooks,
  guarded global teardown, safe pinning, and host-resource accounting retain
  the decisions in ADR 0033.
- Compiler-produced scalar execution completes with zero allocations and zero
  live objects.
- Bytecode loaded from bytes is untrusted and must validate before execution.

Relevant sources include ADRs 0008, 0009, 0012, 0029, and 0033,
`docs/e1-scalar-execution-plan.md`, `docs/e1-talk-runtime-reuse-audit.md`, and
`docs/r1-managed-storage-contract-sketch.md`.

### Modules and packages

- Only packages reachable from the selected root are supplied.
- Locked path, tar, and Git source contracts remain exact.
- Global initialization remains deterministic and once-only.
- If separately compiled modules are introduced, external identity remains
  exact and has one compatible supplier.

The new implementation must first test whether compiling the reachable source
graph as one unit is simpler. It must not recreate scalar implementation
recipes, generated global readers, or a general linker until an observable
behavior requires separate compilation.

Relevant sources include ADR 0023 and the package/linking rows in the parity
ledger.

## Decisions reopened

A new architecture ADR must supersede the implementation-shape requirements of
ADRs 0019 and 0032 before backend code is restored. In particular, the following
are not presumed:

- the current canonical TypedProgram item store;
- exhaustive validation between private, single-producer internal phases;
- the current CheckedMir and TalkIrModule enum surfaces;
- proof wrappers for compiler-generated in-memory values at every seam;
- fixture-only feature representations;
- the G0-G5 checklist for every narrow behavior;
- separate compilation of every source package;
- imported scalar recipes and generated scalar-global accessors;
- the current provenance graph materializer and verifier;
- one negative fixture at every phase for the same semantic mistake.

The semantic ownership of typing, MIR, lowering, and targets remains. Their
current interfaces do not.

## Target architecture

The external compiler interface should remain small:

```text
compile(typed program, entry, target configuration) -> executable or diagnostics
execute(executable, host IO) -> result or runtime failure
```

The backend implementation may use private phase representations:

```text
frontend result
  -> source MIR and ownership checking
  -> monomorphic target-neutral IR
  -> bytecode encoding
  -> validated bytecode execution
```

These are implementation stages, not independently extensible public modules.
A new seam is introduced only when at least two real adapters require it.

### Trust policy

Full validation belongs at real trust seams:

- source/module data loaded from outside the process;
- separately compiled module artifacts, if introduced;
- serialized target-neutral IR, if introduced;
- bytecode loaded from bytes;
- host calls and unsafe memory interfaces.

Private values produced and consumed inside one compiler invocation use normal
construction invariants, focused assertions, and tests through the backend
interface. They do not require a second implementation that re-proves every
producer decision.

Ownership checking is real semantic work and remains mandatory. A duplicate
post-checker that replays the same ownership algorithm is not.

### Provenance policy

MIR operations are the source of successful ownership and borrow explanations.
A query walks those operations and returns only the requested explanation.
There is no eagerly materialized whole-program provenance graph and no second
verifier for a graph derived from already checked MIR.

Rejected programs construct their explanation while the ownership checker still
has the failed transition and relevant path state. Rendering is presentation,
not another semantic phase.

### Target policy

Bytecode is the only parity backend. C, Swift, and browser embeddings call that
same backend. Independent Wasm, C translation, Cranelift, and LLVM adapters wait
until feature parity and the size target are both met.

## Reset procedure

1. Tag the current branch so every experiment, test, and implementation remains
   recoverable.
2. Create the new implementation branch from `a1d20d27`.
3. Bring forward the parity ledger, frozen outputs, reviewed semantic decisions,
   and black-box test harnesses without bringing forward backend implementation.
4. Audit post-`a1d20d27` frontend changes individually. Keep a change only when
   it is independently required for frontend correctness or the first failing
   backend behavior. Do not cherry-pick the current canonical TypedProgram stack
   wholesale.
5. Add the architecture ADR that supersedes the implementation portions of ADRs
   0019 and 0032.
6. Record exact production, test, and documentation baselines for the archived
   backend and the reset branch.
7. Keep `core/Array.tlk` unchanged during the reset.
8. Restore backend behavior only through the execution waves below.

The current rewrite is a quarry: tests and small implementations may be copied
after review, but no commit is integrated merely because it already works.

## Working model

### Start from observable behavior

Each implementation wave begins with one failing black-box source behavior from
the parity ledger. The first test must use the public compiler or tool interface,
not a hand-built internal artifact.

The implementation adds only enough representation and checking to make that
behavior correct. Adjacent unsupported source remains explicitly rejected.
Future variants, fixture builders, and generalized adapters do not land early.

### Consolidate while implementing

Every substantial wave names the existing mechanism it replaces or deepens.
When general behavior supersedes a scalar or local special case, the special
case is deleted in the same wave.

A wave stops for architecture review when any of these occurs:

- more than 1,000 net production Rust lines are proposed;
- the rolling addition-to-deletion ratio exceeds 2:1 after the scalar kernel;
- a semantic rule would be represented or checked in a third place;
- a new module has only one caller and exposes nearly all of its implementation;
- a feature requires a second fixture-only representation;
- the full-parity production budget is projected to be exceeded.

Crossing a stop condition is not automatically forbidden, but it requires an
explicit decision before implementation continues.

### Test the deepest interface

A wave normally requires:

- one source-level acceptance or rejection test;
- one reviewed observable result or diagnostic;
- resource accounting when execution allocates or owns resources;
- a focused algorithm test only for logic that black-box behavior cannot
  isolate;
- malformed-input tests only at real trust seams.

It does not automatically require parallel fixtures and negative tests for
TypedProgram, MIR, target-neutral IR, bytecode, and every adapter.

### Keep documentation local

The parity ledger records behavior status and the architecture ADR records
long-lived decisions. This plan records execution order. Do not duplicate every
contract shape across an ADR, a concrete-contract document, a status document,
and a phase plan.

## Execution waves

Waves are ordered by the next smallest set of complete user behaviors, not by
speculative compiler features. The original wave text is kept below as written,
because the decomposition was right; the 2026-07-17 audit reopened specific
waves by attaching the reference exit criteria each one was missing. Reopened
scope appears inside each wave as a dated block.

### 1. Scalar kernel

Restore Unit, Bool, Int, Float, locals, branches, loops, direct calls, and normal
operator syntax through bytecode. Use signed 64-bit semantics and counted
execution from the start.

The scalar kernel establishes the backend interface and size-reporting tool. It
does not include packages, generic module supply, provenance infrastructure, or
additional targets.

### 2. Copy aggregates and patterns

Drive this wave with `tuple_access.tlk`, then the smallest record and enum cases
needed by `iterate_and_match.tlk` and `string_patterns.tlk`.

Add construction, projection, tags, payloads, and pattern CFG only as those
programs require them. Keep target layout private to the bytecode adapter. Do
not add affine cleanup or managed heap policy to the Copy representation.

**Reopened 2026-07-17 (F2).** "Only as those programs require them" left
record patterns and record destructuring unbuilt, because no driving program
used them; the reference shipped both. Complete the wave with
`match r { { x, y: 123 } -> … }` and `let { x, y } = …` over the existing
tuple-layout record representation (patterns over rows follow the same
row-typing discipline the checker already uses — Gaster & Jones, 1996).
Exit: the StructuralTyping example plus the record-pattern pins from G6.

**Closed 2026-07-17.** One backend helper (`record_cells`) owns the
name-to-slot rule; every pattern site expands records to positional
cells and reuses the tuple machinery, per deepening obligation 4.
`label: pattern` binds the label in addition to the sub-pattern (the
reference lowering binds both names); `label: _` folds into a plain
bind. Open rows and double-ownership cells (a field and its interior
both bound on a consumed value) reject fail-closed with tests. The
reference's two record pins are ported; StructuralTyping is pinned in
G5 (prints `true`). Known boundary, unchanged from tuples: destructured
top-level binders read from inside another function hit the once-only
global storage rejection (wave 7 territory; records additionally fail
in the checker rather than the backend — noted for the wave 7 replay).
Deepening pass folded in: `variant_case` (one owner for variant
tag/payload resolution, was duplicated across test and settle arms),
`tuple_element_tys`, and `strip_borrows` (27 hand-rolled loops; the
pattern-path sites now use the helper, remaining sites convert as
their waves touch them).

### 3. Ownership and deterministic cleanup

Drive this wave with `conditional_moves.tlk` and `clone_method.tlk`.

Implement affine transfer, replacement, path-sensitive cleanup, and the minimum
borrow checking required by real source behavior. Source MIR owns the decision;
target lowering consumes explicit operations. Successful explanations query
MIR only after the checker works.

**Reopened 2026-07-17 (C, F5).** "The minimum borrow checking required by real
source behavior" was the proxy exit: rejection behavior cannot be driven by
passing programs. The reference's 219 flow-rule tests are this wave's actual
specification — NLL-style last-use liveness (RFC 2094), per-argument borrow
provenance (moving an owner invalidates its borrows), partial moves with
sibling-field tracking and field restore, loop-carried move detection, and
call-site marker validation (ADR 0018). Port them as accept/reject pairs;
where MIR consume/retain semantics make a reference-rejected program actually
safe, the divergence is argued in writing, never defaulted into. Unique types
(`*String`, F5) also belong here: they are ownership qualifiers, not a
collections feature. The capture-mode slice of the rules rides with wave 5,
where captures are implemented. Suspected residents of this wave from the G3
burn-down: the `push_block` double frees (let-else, for-loop body argument)
and the assignment-in-if-condition double free — confirm by diagnosis, not by
family name.

**Burn-down progress (later 2026-07-17):** ten ownership defects
fixed against the corpus — Deinit hooks (scope exit, existential
payloads, region finalizers via a synthesized `heap_teardown` chunk
that also frees object-held buffers), explicit initializers on `'heap`
structs, region-claim double-counting (donation is solely
`retain_value`'s job; guards widened to buffers-or-objects), heap
retain glue no longer recurses structurally (a recursive node type
overflowed the compiler), returns donate for place reads (core's
manual buffer code exempt), global-init sinks donate, break-path
ownership states merge at loop exits through `merge_arms`, and
deconstruction transfers ownership to extracted elements. The list
stands at 70. A wording-repin audit also restored eight
reference needles that had captured runtime crashes as diagnostics —
those rejects are the by-value move-discipline family, honestly
failing now.

**Check mode landed (later 2026-07-17):** `TALK_CHECK_ALL` compiles
every user callable — generics rigidly — with a synthesized entry for
declaration-only programs, so the whole corpus now exercises its rules
the way the reference's whole-program pass did; the flow gate runs
under it. The by-value move-discipline family closed (globals track
moves path-sensitively through the arm-merge machinery; the explicit
`copy` marker clones at the argument site), and the new coverage
surfaced and fixed three checker precision bugs (arm-merge union
seeding, borrow bindings marking their sources, borrow-annotated lets
as loans). The gate enforces 123 of 183; the 60-name remainder is the
deep provenance block: owner-move/reassignment invalidating live
borrows, escaping-borrow returns (substrings, borrow-carrying
containers), borrow-typed fields and payloads, linear-value
path-sensitivity, loop-carried moves and borrows, unique `*T`
parameters, and marker validation.

**Provenance and liveness landed (later still, 2026-07-17):** borrow
provenance (views map to the frame local they derive from, propagated
through binds, fields, tuples, variants, and constructions) powers the
escaping-borrow return family and owner-move/reassignment
invalidation; source-order last-use liveness (the frame scan counts
uses, each read spends one) powers the live-loan conflicts — reading a
mut-borrowed owner, mutating a shared-borrowed one, moving any
borrowed owner, and mut-argument/receiver invalidation of shared
views. Structural rules joined: borrows cannot be stored in fields,
payloads, or temp-rooted globals; call-site markers must match
declared modes; `copy` requires cloneability. At this checkpoint the
gate enforced 146 of 183 with every other gate green; the final
burn-down is recorded in the closure note below.

**Closed 2026-07-17.** The corpus is ported
(`tests/reference/flow`: 110 accepts, 73 rejects;
`reference_flow_corpus_holds`) and enforces 170 of 183 rules. The
burn-down went 101 → 170 through: `TALK_CHECK_ALL` (every declaration
compiles, generics rigidly via self-substitution — closing all 44
declaration-only rejects); global move discipline threaded
path-sensitively through match arms; borrow provenance
(view-recording, owner invalidation, escaping-return rejection) with
source-order liveness for exclusive/shared conflicts (non-lexical
lifetimes in the sense of RFC 2094: a loan dies at its last use, not
its scope end); loop-carried move detection over back-edges; the
structural family (stored borrows, marker misuse, heap placements,
rvalue-to-mut); unique `*T`; the linear family with sanctioned
disposals (consuming receivers, owned consume-parameters,
abort-unwind cleanup); and extraction-through-shared-borrow gated on
Copy/CheapClone conformance, including rigid parameter bounds.

The 13-name tail, argued or open: `rejects_borrowed_global`,
`rejects_whole_struct_use_after_owned_field_move`, and
`rejects_function_assigning_a_globally_borrowed_global` (argued:
donation and static-literal semantics make these programs sound
here); the raw-pointer pragma pair (needs `// unsafe` source-pragma
plumbing from driver to backend); `borrowed_marker_struct_cannot_
escape_its_loan` (loan escape through struct fields);
`loop_carried_mutable_borrow_lives_until_storage_dead` (loop-carried
loan liveness); the two handler/trailing-block may-move rejects
(block-closure move propagation);
`generic_early_consume_auto_clones_without_marker` (auto-clone at
early consume); the two rigid-compile witness gaps (protocol default
receivers, witness-call releases); and `tuple_match_keeps_owned_and_
borrowed_payload_drops_separate` (mixed-ownership tuple payload
accounting). Each is a refinement of an existing component, not a
missing one. Argued divergences recorded: demand-driven checking of
declaration-only programs, and reject pins carrying this compiler's
own diagnostic wording where the rule fires.

### 4. Managed values and core collections

Drive this wave with `string_building.tlk`, `graphemes.tlk`,
`string_patterns.tlk`, `iterate_and_match.tlk`, and `heap_graph.tlk`.

Implement managed bytes, String, Character views, Storage, Array, Dict, clone,
destroy, deinit, CoW, and heap regions in that order. Apply ADR 0033 policies
only when the next program requires them. Resource accounting is mandatory for
each step.

**Reopened 2026-07-17 (F6, V slice).** The implementation exists but was never
measured against the reference's pins. Port the string/UTF-8 boundary cluster,
the iterator-adapter cluster, and the heap/region cluster (aliasing, cycles,
deinit-at-teardown, resurrection trap, drop-once/leak balances) from the 220
VM tests as this wave's G6 slice, and verify `for x in consume xs` /
`for x in mut xs` against the reference's iteration-mode pins.

**Closed 2026-07-17.** 61 reference tests ported as three corpus
clusters (strings/UTF-8 incl. the U+FFFD decode boundary table,
collections/iterators incl. every iteration mode, drop-once/leak
balances; the reference file holds no heap-region tests — that
machinery's pins remain this repo's own). The port caught three real
defects on arrival, all fixed: `for x in mut xs` failed the writeback
convention everywhere (initializers registered writeback slots for
exclusive-borrow parameters that constructions never unpack — F6
confirmed broken, now verified green); iterator adapters leaked one
allocation (`consume_into` retained through Borrowed-classified views,
counting references view drops never release); and or-patterns binding
owned payloads in every alternative were rejected by a conservative
leaves-owned-unbound (now recursing through variant payloads via
`variant_case`). G6 stands at four clusters, 79 pins, all green.

### 5. Closures, existentials, and indirect calls

Restore noncapturing function values first, then captures, cells, recursive local
functions, existential payloads, and dynamic witness calls as required by the
remaining corpus. Do not introduce a general closure or witness-table format
before two real source shapes need it.

**Reopened 2026-07-17 (F1, F3, C capture slice).** Cells were in this wave's
scope from the first draft (the sentence above) and were dropped when ledger
row CHG-06 narrowed captures to "Copy and shared borrows only" without a plan
review. Complete the original scope: mutable captures via cells (assignment
conversion — the standard Scheme-compiler treatment, e.g. Kranz et al., ORBIT,
SIGPLAN 1986; Appel, *Compiling with Continuations*, 1992), plus the explicit
capture lists `[consuming s]`, `[&s]`, `[copy s]`, with the reference's
capture-mode flow rules ported alongside as this wave's slice of C. Inferred
(unannotated) generic functions (F3) also close here — `func fib(n)` fails at
a conformance-dictionary boundary, and dictionary demand for inferred schemes
is witness machinery, not effects machinery (Wadler & Blott, POPL 1989).
Exit: the closure/cell cluster of G6 plus the Capture, Counter, and Fib
examples. Diagnose here first: the Identity/Show example leaks (S2, likely
witness glue) and the `method_decl` double-free family from the G3 burn-down
(dispatch/writeback) — confirm by diagnosis before assigning.

**Closed 2026-07-17.** Cells landed exactly as the runtime already
shaped them: the VM's CellNew/CellGet/CellSet (opcodes 9-11, kept from
the reference lineage but never emitted) now carry assignment-converted
bindings — a symbol assigned anywhere in a frame and referenced under a
nested function value binds through a cell; the closure and the frame
share the (copyable) handle. Reference pins ported: makeCounter,
independent counters per activation, top-level mutation visibility,
capture of a rebound binding, recursive closures capturing locals
(letrec through a celled binder), and local self/mutual recursion.
Capture lists enforce the reference's rules: completeness against an
explicit list, `copy` requires a copyable type, `consuming` moves the
owner. F3 closed via `demand_specialized`: a scheme parameter the
recorded instantiation leaves unbound takes the enclosing instance's
binding (typing keeps recursive uses monomorphic), which is the static
sub-dictionary rule. S2's diagnosis found neither witness glue nor
anything Show-specific: `return` never flushed statement temporaries,
leaking every intermediate of a chained-concat return — one line fixes
Identity and Show, and FileIO/TrailingBlock were pin-generation
artifacts (the reference harness reads stdout and the final value
separately; the pins now carry the CLI's trailing-value line over the
byte-identical stdout). G5 stands at 15 of 16 pinned green; Imports
(wave 7) is the only burn-down entry left.

Argued divergences, fail-closed with tests: consuming/borrow captures
of owned (droppable) values reject until closure drop glue exists — the
reference never executed one on its VM (its flow tests only pin
acceptance, its evaluator was refcounted); generic local functions that
capture reject (a closure compiles once per frame and cannot specialize
per call); cells hold copyable values only (ownership-sensitive mutable
captures reject, matching the reference's UnsupportedClosureCapture).

Deepening pass folded in: `capture_env`/`bind_env` are now the single
build/bind pair for closure environments (func closures and block
closures shared ~70 duplicated lines; handler clauses next when wave 6
touches them) — the declared extension point for wave 6's capability
slots; `cell_celled_params` dedupes parameter conversion; the dead
`_expr` parameter left `compile_closure`.

### 6. Deep one-shot effects

Drive this wave with `handlers.tlk`, then `caller_locals_handler.tlk`,
`nested_handlers.tlk`, `resume_across_frames.tlk`,
`multi_effect_handlers.tlk`, `generic_state.tlk`,
`generic_two_instantiations.tlk`, and `effectful_closures.tlk`.

Implement dynamic nearest-handler routing, one-shot Resume/Discontinue, cleanup
of abandoned frames, generic effect state, and checked captures directly in MIR
and the target-neutral executable form. Do not restore capability-passing CPS or
lambda-G.

**Reopened 2026-07-17 (S1).** The paragraph above under-specified the routing
rule. Dynamic nearest-handler search is correct only for performs evaluated in
the frame that syntactically contains them; a *function value* must capture
the handlers of its creation site and perform against those, per ADR 0011
departure (d) — effects as capabilities (Brachthäuser, Schuster & Ostermann,
OOPSLA 2020). The reference pins `f() + 'boost()` under two nested handlers at
300; dynamic search gives 400 — a silent wrong answer, the worst defect class.
Closures therefore carry capability slots in their environments for the
effects their bodies perform; this lands after wave 5's cell/capture-list
rework so the environment layout is rebuilt once, not twice. Also diagnose
here: the effect-typed-function and inline-IR leak family from the G3
burn-down. Exit: the full effects cluster of G6 (deep handlers, conditional
resume/abort, tail/statement performs, handler locals) plus the lexical
capture pin.

**Closed 2026-07-17.** A capability is what `FindHandler` already
produced — the handler's clause value and stack index; lexical capture
is evaluating that pair at closure creation instead of at the perform.
Closures carry one `(clause, index)` per user effect in their resolved
row as environment slots through `capture_env`/`bind_env` (the wave-5
contract point, extended exactly there); a perform routes through the
frame's captured capability when it has one and dynamic nearest-handler
search otherwise, so every existing behavior (clause-outside-own-handler
CHG-01, nested handlers, resume across frames) is unchanged. The
capture pin prints 300. The reference's entire user-effects suite — all
18 tests — is ported as the G6 effects cluster
(`tests/reference/effects/`, `reference_effects_cluster_matches_frozen_stdout`)
and passes: aborts at depth, abort-value-as-scope-value, conditional
resume/abort, tail/statement/expression performs, repeated performs
through one deep handler, handler locals, effectful closures stored in
struct fields, and per-function handlers. The G3 leak family (F4) fell
earlier, to wave 5's return-path fix. Scope notes: trailing blocks run
within their call's extent (dynamic and lexical agree) and carry no
capabilities until a pin demands them; named functions used as values
stay on the dynamic path (the reference pins only in-extent calls);
handler clauses keep their delimiter/floor machinery. The runner merge
also landed: `assert_corpus_program`/`assert_corpus_dir` are the one
corpus mechanism behind G2, G5, and G6 (deepening obligation 6).

### 7. Modules, packages, IO, and tools

Add whole-reachable-graph package compilation first. Introduce separately
compiled module artifacts and a linker only if a required behavior cannot be met
without them.

Restore host IO, package run/test, REPL execution, bytecode emission,
standalone execution, and embeddings through the same bytecode path. Preserve
exact locked source supply and deterministic globals.

**Reopened 2026-07-17 (F4, S2 slice).** Multi-file `talk run` (the Imports
example) traps on an arena handle, and FileIO diverges from its frozen stdout
— both are this wave's surface. The `_copy` invalid-pointer import family
from the G3 burn-down is suspected here too. Exit: Imports and FileIO leave
G5's known-failing list; the module/package pins from G6.

**Closed 2026-07-17.** The arena trap was initialization order:
multi-file scripts composed files in discovery order, so an importer's
statements ran before its imported sibling's globals stored.
`files_in_initialization_order` hoists a file's local imports ahead of
it (depth-first, insertion-stable — a first layer-based attempt moved
the test harness postlude out of last place and was fixed the same
day), and both the script and named-entry paths compose through it
(LINK-02). The `_copy` import family turned out to be the construction
ownership bug (see the burn-down note below), not a loader issue —
there is no second loader path to delete. G5's burn-down list is
empty: all 16 pinned examples pass.

### 8. Parity closure and simplification

Replay every Required ledger row and all 16 complete programs. Remove temporary
special cases, unused variants, duplicate checks, obsolete documentation, and
one-adapter seams before declaring parity.

A final size and architecture review is part of parity, not post-parity cleanup.

**Revised 2026-07-17.** Closure now means gates G1 through G6 green (G5's
known-failing list empty, every G6 cluster ported or argued) — not ledger
rows and self-authored programs alone. The size review stands.

**Closed 2026-07-17.** Every gate is green at once: G1 18 core tests,
G2 16 frozen programs, G3 talk-syntax 225 (224 suite + composed) and
talk-html, G4 embeddings, G5 16/16 examples with an empty burn-down,
G6 four clusters (79 pins), and the wave-3 flow gate at 170 of 183
with its 13-name tail argued or catalogued above. Workspace total: 950
tests. The size review ran with each wave's deepening pass (session
rule: after every wave, look for chances to deepen an existing
component before adding a new one); the final sweep removed the ad-hoc
backend debug probes and the dead root-library compile in
`compile_graph` (both call sites re-parse root sources and read only
the dependency map). The backend stands at ~10.4k lines across
`mir.rs` and `lower.rs`: one instruction-building pass with
frame-local ownership state, one lowering pass, no IR beyond the
instruction list.

### 9. Drop emission rework

**Designed 2026-07-17; not started.** Profiling after parity (see the
performance commits `c2677e35`, `155fbf8d`, and the published profile
report) showed drop code generation is the largest single backend
cost: the drop family (`drop_value`, `drop_scopes_from`,
`unwind_cleanup`, `drop_enum_value`) accounts for ~30% of backend
compile time, and 13.3% of all emitted instructions (19,060 of
143,099, in 2,714 blocks) are unwind-cleanup code for effect-abort
paths that almost never execute (46 k executed `Free`s against 28.8 M
total executed instructions). The cause is not the ownership model —
placement is already tight — but three emission choices that make
code generation O(sites × type size × catalog size) where the
reference designs are additive:

1. structural drops are macro-expanded inline at every drop site
   (field walks, and a full per-variant tag dispatch for enums — on a
   parser corpus the dying values are large AST enums, so each site
   expands to dozens of instructions);
2. every suspendable call synthesizes a fresh cleanup block that
   re-drops the entire live set from scope 0, after cloning three
   tracking maps — O(calls × live values);
3. every nominal drop re-queries the world: `deinit_witness` scans
   every program's whole conformance map per drop, and `needs_drop`
   re-walks type structure per field per site.

The rework has three parts, in dependency order:

**9a. Memoized drop queries.** A canonical `Deinit` index
(symbol → witness and self-args) built once in `ProgramBuilder::new`,
exactly like the struct/enum/conformance indexes that closed the
first performance pass, replaces `deinit_witness` /
`is_deinit_witness` scans; a `needs_drop` memo keyed by `Ty` (types
hash and compare already — the glue map uses them as keys) replaces
repeated structural walks, with `contains_object` / `contains_buffer`
candidates for the same cache. Measured target: the 18.9% inclusive
`deinit_witness` share and part of the `canonical`/`Symbol::eq`
cluster. No emission-shape change; the drops corpus pins behavior.

**9b. Shared per-type drop functions.** `Glue::Drop` and
`value_glue(ty, Glue::Drop)` already build exactly the needed
function — one synthesized teardown body per type, today used only
for existential witness tables. Ordinary drop sites route through it:
a site emits one `Call` to the type's drop function instead of the
inline expansion, so a type's field walk and enum tag dispatch are
emitted once per program rather than once per site (the shape of
Rust's per-type `drop_in_place` shims and Lean's per-type `dec`
functions — Ullrich & de Moura, *Counting Immutable Beans*, IFL
2019; Perceus's drop specialization, Reinking, Xie, de Moura &
Leijen, PLDI 2021, then selectively re-inlines the shared routine
only where reuse analysis pays, which presumes the shared routine as
the baseline). Two carve-outs: trivial drops (a single
`Free`/`RegionRelease`) stay inline — a call would cost more than it
shares — and types whose glue needs rigid-parameter witnesses
(`glue_witness_params` non-empty) keep the inline path, as their
sites already hold the witnesses. The `Deinit` hook ordering (body
first, then structural field teardown) moves into the glue body
unchanged; the deinit-order reference pins are the gate. The
small-function inliner cannot re-expand what this pass shares:
`Free`, calls, and multi-block tag dispatches are all outside its
candidate whitelist — assert that with a test, not a comment.

**9c. Cleanup chains.** Replace per-call-site cleanup synthesis with
one lazily-built chain per function: each node drops exactly one
owned value (via 9b's shared functions, so a node is one or two
instructions) and jumps to the next node toward the outermost scope;
the innermost node a call site needs is its unwind target, and the
outermost terminates in `UnwindRet`. Total cleanup code becomes
O(live values) per function instead of O(call sites × live values) —
the shape of MIR drop elaboration in Rust and of shared landing pads
in zero-cost exception handling (de Dinechin, *C++ Exception
Handling*, IEEE Concurrency 2000). The design leans on an invariant
Talk's move rules already provide and `merge_arms` already enforces:
a local moved on one arm is dropped at the end of every arm that
still owns it, so **the owned live set is path-independent at every
join** — the chain is fully static, with no runtime drop flags (the
mechanism Rust needs because it permits conditional moves). Chain
maintenance mirrors the owned stack: push on bind or temp
registration, invalidate the materialized prefix above a mid-stack
consume (moves are not LIFO; nodes below stay valid), and
debug-assert chain equality across arms at every join. Expected
effect: the 13.3% cleanup share of emitted instructions collapses to
a few nodes per function, and every downstream pass (liveness,
intervals, lowering) shrinks with the instruction count it iterates.

Exit criteria: all gates green — the drops corpus's exact allocation
balances and deinit-order pins are the semantic net — plus a
`talk mir`-level test that a function with two drop sites of the same
enum type contains one tag dispatch, and one with several calls at
equal depth contains one cleanup chain, not one block per call.
Measured targets: backend compile ≈400 ms → ≈250 ms on the
talk-syntax corpus, emitted MIR ≈143 k → ≈120 k instructions, with
execution unchanged or slightly better (frame widths shrink as
cleanup blocks stop minting per-site locals).

**Closed 2026-07-17** (commits `e09a28b7` 9a, `8350e3b7` 9b,
`a01c59d9` 9c). The targets were conservative: sharing the per-site
structural expansions removed far more than the cleanup share alone.
Measured on the talk-syntax corpus — MIR: 143,099 → 42,711
instructions (−70%), 47,019 → 14,205 blocks; unwind cleanup: 19,060
instructions in 2,714 blocks → 714 in 367 (13.3% → 1.7% of emitted
code); wall: 1.29 s → 0.89 s (compile 0.68 s → 0.37 s); the whole
`talk test` run is 8.28 s → 0.89 s since profiling began (9.3×). Two
shape tests pin the design (`structural_drops_share_one_teardown_body`,
`unwind_cleanup_is_one_chain_per_function`), and all gates stayed
green at each of the three steps: 962 workspace tests — the effects
cluster's abort pins and the drops corpus's exact balances included —
18 core, 225 talk-syntax, 1 talk-html.

### 10. Emitted-code quality: coalescing, bitsets, block constants

**Closed 2026-07-17** (commit `43c6c050`). Four measured fixes:
copy coalescing by register hints in the interval allocator (a
`Copy` whose source interval ends exactly at the copy takes the
source's register, and lowering elides `dest == src` moves — Wimmer
& Mössenböck, VEE 2005; safe at equal positions because the VM reads
an instruction's operands before writing its destination, and hints
only ever pair a copy with its own source, so multi-destination
instructions never share); dense-bitset live sets in the dataflow
fixpoint; a flat module-alias table behind `canonical()`; and a
per-block constant cache in lowering. Executed `Move`s fell from
8.48 M (29.4% of all VM instructions) to 0.66 M (3.1%); the suite
runs in 0.81 s (compile 0.35 s). The constant cache underperformed
for a measured, structural reason recorded in wave 11's motivation.

### 11. SSA-form MIR

**Designed 2026-07-17; not started.** The remaining execution waste
is now measured precisely (opcode histogram after wave 10, ~21 M
executed VM instructions): `Const` is the single most-executed
opcode at 4.35 M (~22%) — the per-block cache cannot help, because
the repetition is loops re-materializing the same constants on every
iteration, and nothing short of dominance-aware placement can move a
load out of a loop. Residual `Move`s (0.66 M), the inline splice
`Jump` chains (1.6 M), and the compile-time cost of emitting copy
chains at all are the same story: the builder models values as
mutable registers, so every fact about a value's identity is
rediscovered downstream. Static single assignment makes value
identity the IR's invariant instead (Cytron, Ferrante, Rosen,
Wegman & Zadeck, TOPLAS 1991; the field survey is Rastello &
Bouchez Tichadou, *SSA-based Compiler Design*, Springer 2022).

**Form.** SSA with block parameters rather than φ-nodes: a block
declares parameters, and each predecessor's terminator passes
arguments (`Goto(target, args)`, `Branch { …, then_args, else_args }`).
Block-parameter form is the same theory (a block is a local function
— Appel, *SSA is Functional Programming*, SIGPLAN Notices 1998;
Kelsey's CPS correspondence, 1995) with two practical advantages:
no φ-ordering subtleties, and the out-of-SSA moves are explicit on
the edge rather than implicit in node position. It is the form used
by the IRs this backend most resembles (Cranelift, MLIR, Swift SIL).

**Construction.** Braun, Buchwald, Hack, Leißa, Mallon & Zwinkau,
*Simple and Efficient Construction of SSA Form*, CC 2013: the
builder keeps a per-block map from source variable to current value,
`readVariable` recurses through predecessors, unsealed blocks (loop
headers under construction) get incomplete parameters completed at
seal time, and trivial parameters (all arguments equal) are elided
on the spot. This algorithm is designed for exactly our shape — a
single pass straight off the AST, no dominance computation, no
separate rename phase (the Cytron construction needs both). Three
consequences fall out for free:

- a `let` binding is a map entry, not a `Copy` — the instruction
  and its downstream Move cease to exist;
- a constant is a value defined once at its first dominating use —
  loop bodies reference the value, and the 4.35 M per-iteration
  re-materializations collapse to one load per constant per
  function entry path;
- def–use information is exact, so the NLL liveness scan
  (`use_counts`) and the interval builder stop re-deriving it.

**Ownership on SSA.** The ownership machinery gets simpler, not
harder, and the invariants sharpen:

- `moved` becomes monotone: a value, once consumed, never
  un-consumes (reassignment creates a new value; the assignment
  drops the old one exactly as today). Path-sensitivity reduces to
  "which value reaches" — the thing SSA computes by construction.
- `merge_arms`'s reconciliation is unchanged in substance: arms
  still drop divergently-moved values at their ends, and the wave-9
  invariant becomes "a block parameter is owned on every incoming
  edge or on none."
- Borrow provenance, views, and loans key on values instead of
  mutable slots — strictly sharper, since reassignment can no
  longer conflate two lifetimes under one local id.
- The cleanup chain (9c) is untouched: nodes hold value ids.

**Out of SSA and allocation.** The linear scan extends to SSA form
(Wimmer & Franz, *Linear Scan Register Allocation on SSA Form*, CGO
2010): one interval per value with use positions, block-parameter
edges contributing coalescing hints — the generalization of wave
10's copy hints, so most edge arguments allocate into their
parameter's register and no move is emitted. Residual edge moves
are parallel-copy semantics and follow Boissinot, Darte, Rastello,
Dinechin & Guillon, *Revisiting Out-of-SSA Translation*, CGO 2009:
split critical edges, sequentialize each edge's parallel copy,
break cycles with one temporary. (Chordal-graph coloring — Hack &
Goos, CC 2006 — is the alternative if interval precision ever
disappoints; on SSA the interference graph is chordal and optimal
coloring is polynomial, but the linear scan is already in place and
Wimmer-Franz is its published SSA evolution.)

**Phasing** (gates green after each, opcode histogram re-measured):

- **11a. Copy folding in the builder.** Value aliasing at bind and
  copy sites through the existing MIR — a `Copy` from a value
  becomes a map entry, no instruction; `LocalId` doubles as the
  value id; no CFG or `Term` changes. This is Braun's construction
  restricted to straight-line facts, and it alone should remove
  most static `Copy`s and their compile cost. Exit: a shape test
  that a let-chain function lowers with zero `Move`s; executed
  `Move` share re-measured.
- **11b. Block parameters.** `Term` grows argument lists; Braun
  `readVariable`/`writeVariable` with sealing replaces the direct
  local writes for reassigned variables and loop carriers;
  `merge_arms` produces parameters instead of writing a shared
  local. Constants become entry-block values. The inliner remaps
  arguments; `talk mir` renders parameters. Correctness first:
  lowering emits every edge move naively.
- **11c. SSA linear scan.** Intervals per value, edge hints,
  Boissinot resolution; delete the per-block constant cache
  (subsumed) and wave 10's special-case copy hints (generalized).
  Exit: executed `Const` ≤ 8% and `Move` ≤ 3% of instructions,
  total executed instructions ≤ 16 M on the talk-syntax suite.

**Consumers to audit before 11b:** `render_mir` (`talk mir`), the
small-function inliner (argument remapping), the register allocator,
and any scalar-compiler path that reads `mir::Inst` (the wasm/talk-c
E2 lineage) — enumerate with the compiler, not by memory.

**Risks.** The ownership bookkeeping keys on `LocalId` across
`mir.rs`; 11a confines the change to the value-map lookup points
(bind and read sites), which is why it goes first. Diagnostics must
keep naming source variables — the variable map carries the symbol
alongside the value. The flow corpus's reject pins are
fragment-based, so sharpened provenance must not reword them; the
183-program gate is the check. Loop sealing order is the one
subtle piece of Braun construction — incomplete parameters must be
completed exactly when the last back edge is known; the loop
compilation sites (`while`, `for`, recursion through handlers) each
need a seal point and a test.

**11a closed 2026-07-17** (commit `1d20c13b`): bindings alias their
owned rvalue temporaries through `bind_owned_pattern` — lets, tuple
elements, and match-arm payloads in one arm — with a shape test
pinning zero copies in a let chain. All gates green (964 workspace).

**Checker findings, 2026-07-17** (commit `48d5f512`). `VarStore::find`
already compressed unsolved paths; the gap was chains of *solved*
variables re-walked and re-cloned per query — `shallow` now compresses
them onto the entry variable's binding (Tarjan's amortization applied
to the solved half; two unit tests pin it). Hash-consed / Rc-shared
`Ty` payloads were probed and deliberately declined: converting
`Nominal` alone surfaces 94 compile errors (~300 edit points for all
variants) against measured `Ty` clone+drop traffic of ~6–7% of
compile — 15–20 ms of a 750 ms run. The checker's 19% share is
dominated by constraint-solving work itself, not clone traffic;
attacking it means profiling `check_types` / `Solver::solve`
internals (constraint volume, retry behavior, binding-group
scheduling), not representation changes. That is the honest next
lever on the compile side.

**11b/11c closed 2026-07-17** (commit `a3efe2c2`), with one deliberate
narrowing. Landed: block parameters on `Goto` edges (`BlockData`
declares parameters, `Goto` passes arguments; `Branch` stays
argument-free because merged values always route through dedicated
arm blocks, so critical-edge splitting never exists); `merge_arms`
passes each arm's value as an edge argument instead of copying into
a shared result local; the allocator treats parameters as block-entry
definitions and coalesces a dying edge argument onto its parameter by
hint (11c's substance — the copy-hint mechanism generalized, one
map); residual edges lower as parallel copies with cycle-breaking per
Boissinot et al., CGO 2009; the inliner remaps parameters and edge
arguments. Deferred: Braun `readVariable`/`writeVariable` with
sealing — reassigned variables and loop carriers keep their mutable
locals. Post-RK that conversion buys IR uniformity, not measured
counts (assignment copies are a small static population and the
loop-carried values are genuinely multi-def), and it is the one piece
whose cost lands squarely on the ownership bookkeeping; it should be
its own wave with its own motivation if the IR ever needs full SSA
(e.g. for value numbering or code motion across joins). Unit test
pins edge coalescing; all gates green at 965 workspace tests.

**Constants finding, 2026-07-17 (experiment falsified — read before
starting 11b).** A loop-invariant constant-placement pass (entry-
block definitions for constants used inside layout-order loop
intervals) was built, measured, and **reverted**: executed `Const`
barely moved (4.35 M → 4.18 M) while executed `Move` tripled
(0.66 M → 1.6 M, from loop-block `Copy`-from-constant sites turning
into register moves whose sources never die). The opcode histogram
shows why: the 4.35 M constant loads are **per-call materializations
in hot leaf functions** — the loop is in the caller, so no
intra-function placement (entry block, preheader, or SSA value
alike) can amortize them; a frame's registers are born per call.
This also invalidates 11b's "constants become entry-block values"
expectation as a performance claim: do it for IR cleanliness if 11b
proceeds, but expect no constant-count win from it. The candidate
real fixes, for a deliberate decision rather than another bandaid:

- **register-or-constant instruction operands** (Lua 5's RK operand
  design — Ierusalimschy, de Figueiredo & Celes, *The
  Implementation of Lua 5.0*, J.UCS 2005): an operand addresses the
  register file or the constant pool directly, and `Const`
  materialization ceases to exist as an instruction. This is
  instruction-set design, not a compensation for weak compiler
  output — approved and **landed 2026-07-17**: the high bit of an
  operand field selects the 15-bit constant-pool index (overflow
  falls back to materialization), on the arithmetic/comparison
  operands and every argument-pool entry — constants flow into
  calls and constructions with no instruction at all. Executed
  `Const` fell 4.18 M → 1.39 M (the rest sit in non-RK positions:
  copy-from-constant binds, store/IO operands) and total executed
  instructions fell ~21 M → ~16 M, meeting the wave-11 execution
  target before 11b/11c begin. The decoder validates RK fields
  against the pool, the disassembly renders them as `k[n]`, and a
  shape test pins that `n + 1` compiles with no `const`
  instruction;
- **deeper inlining budgets**, so hot leaf bodies (and their
  constants) land inside caller loops where placement then works —
  bounded win, code-size trade;
- accept the load: a `Const` dispatch is among the cheapest opcodes.

Wall-clock note for future sessions: sustained benchmarking
throttled this machine from 4.34 GHz to 3.79 GHz (~13%) across the
session's tail — cross-batch wall comparisons drifted accordingly;
executed-instruction counts were the reliable signal throughout.

## Parallel work

Backend core work is sequential until the external backend interface and the
first two execution waves demonstrate an acceptable cost curve.

Parallel work is limited to genuinely independent tasks such as:

- auditing frozen outputs;
- reviewing source semantics;
- testing an already stable host adapter;
- documenting an accepted decision.

Do not freeze a shallow interface merely to create disjoint implementation
lanes. Two agents do not justify a seam.

## Wave report

Every implementation wave reports:

```text
observable behavior restored
archived oracle used
production lines added/deleted
test lines added/deleted
documentation lines added/deleted
modules added/deleted
interfaces widened/narrowed
semantic rules added and their single owner
special cases removed
unsupported adjacent behavior
commands actually validated
```

The report is reviewed before the next wave begins.

## Final exit

The rebuild is complete only when:

- required bytecode parity is green;
- all required tools and embeddings use the same path;
- allocation and resource balances are reviewed;
- source ownership and effect diagnostics are correct;
- there is no second semantic evaluator;
- there is no fixture-only production module;
- internal validation is limited to real semantic checking or real trust seams;
- the reviewed production size target is met;
- the final architecture passes the deletion test and exposes a small, deep
  backend interface.

Independent backend adapters begin only after this exit.

## Immediate next actions (revised 2026-07-17)

The original reset steps are complete. What remains is replaying the reopened
waves, in dependency order rather than severity order:

1. **Wave 2 completion** — record patterns and destructuring. Small, isolated,
   and it un-blocks the StructuralTyping example.
2. **Wave 5 completion** — cells, capture lists, the capture-mode flow rules,
   inferred generic functions. This reworks closure environment layout.
3. **Wave 6 completion** — lexical capability capture, immediately after wave
   5 so capability slots land on the final environment representation instead
   of forcing a second layout change. (S1 is the most severe open defect —
   silent wrong answers — but doing it before the environment rework would
   build it twice; the two waves together are the correctness unit.)
4. **Wave 3 completion** — port the flow-rule suite and unique types. Largest
   item; independent of the closure work, and it back-stops waves 5/6 by
   rejecting the unsound programs they could otherwise admit.
5. **Wave 4 verification** — port the string/heap/iteration G6 clusters
   against the existing implementation.
6. **Wave 7 completion** — multi-file run, FileIO, import trap family.

The 16 open G3 failures are burned down inside whichever wave their diagnosis
assigns them to — the family-to-wave guesses in the wave blocks are suspicions
to confirm, not assignments.
