# 0027 — Effect aborts unwind through lowerer-emitted cleanup

Status: superseded by ADR 0031 (2026-07-13)

## Implementation notes (2026-07-12)

Landed as specified, with these resolutions/refinements:

- **Deinit rows**: the checker did NOT enforce purity —
  a user effect in a `deinit` witness's row unified silently into the
  requirement's quantified tail. Now enforced at the conformance
  (`TypeError::DeinitEffectRow`, `check_extend`): a `Deinit` hook whose
  solved row carries a non-core effect is rejected; a handler installed
  INSIDE the deinit body stays legal (the row is pure at the boundary).
- **Mid-finalizer aborts**: this falls out of the Deinit-row resolution
  rather than needing new flow modeling. The finalizer thunk's glue
  (witness call + field frees) passes no capabilities, so — with Deinit
  rows enforced pure — the only effectful code reachable during teardown
  is inside the witness under its own `@handle`, whose delimiter is the
  witness's own frame. No abort can ever discard the thunk frame or skip
  its field frees; the witness's own suspension sites get ordinary
  `Unwind` coverage from its own flow pass. Test 5 is green in the only
  constructible shape ("finalizer body performs" = self-handled).
- **Evaluator label identity**: pinned by test 9; one
  refinement was required — an application pops ALL consecutive matching
  top entries, not one: a tail-call chain records several suspensions
  sharing one continuation, all completed by its single application.
- **Block cache**: no new key material was needed —
  `MirCtxKey` already carries `drop_stack`/`drop_flags`/`theta`, which
  determine the entry's content; a cache hit reuses an entry built from
  an equal context.
- **Evaluator UnwindDone**: no distinguished done-continuation needed —
  the entry's body chains its drops down to the ⊥-typed `Op::UnwindDone`
  primop, whose VALUE naturally completes the nested evaluation (simpler
  than `run_finalizer`'s `finalizer_done`).
- **R9/F-B follow-up resolved**: MIR-published entries are now claimed by
  the application before nested capability/trailing-body lowering and
  attached by `lower_value_call` and witness dispatch as well as direct
  calls. Structural lowering tests cover witness attachment and
  `function_value_abort_drops_enclosing_owned_value` balances both engines.
- **F-C follow-up resolved**: resource-carrying aggregate operands materialize
  for every call, with one checked normal cleanup authority; suspending calls
  and performs additionally receive the live temp set from the whole-CFG
  cleanup planner. Object-carrying aggregates qualify even when `needs_drop`
  is false. Flow separately tracks source consumption and runtime transfer, so
  +0 object parameters and performer-owned payloads remain caller/performer
  cleanup even when source-consumed. +0 parameters are runtime-borrowed inside
  the callee, preventing moved fields from racing caller cleanup. Generic temp
  actions survive until specialization (`DropValueIfObject` /
  `ReleaseRegionsIfObject`). Named places and temps share an initialization
  order, so abort cleanup matches normal reverse order. Both-engine matrix
  tests cover normal, resume, and abort.
- The free-balance verifier still ignores unwind operands and abort-only
  entry bodies (its model is normal-path balance), and `Op::Abort` bodies
  remain a counted skip.
- Abort-during-unwind traps on both engines ("abort during abort
  unwinding") — including a `Deinit` hook that internally ABORTS its own
  handler while running inside an unwind entry (an internal RESUME is
  fine: resume is `Ret`).

## Context

ADR 0011 compiled effects to capability-passing CPS and defined abort as
"the handler body finishing into the captured delimiter; the frames
between the perform and the handled scope simply never resume." The
capability closure captures the installing frame's raw machine return —
`install_ctx.raw_ret_k` at `src/lower/effects.rs:203-207` — and an
aborting handler's tail applies it. On the VM that application compiles to
`Insn::CallCont` (the scheduler's bare-value computed-application case,
`src/vm/schedule.rs:326-331`), and the interpreter's unwind discards every
frame above the delimiter wholesale (`talk-runtime/src/interp.rs:273-281`).

ADR 0011's consequences section already named the debt: "Aborts still skip
frame cleanups (drops, region write-backs) between the perform and the
delimiter." The ownership-soundness review (finding B1,
`docs/ownership-soundness-plan.md`) confirmed every shape of that debt
with running repros:

**Shape 1 — the performer's frame.** Every owned local in the frame that
performs leaks: its scope-exit drops live in the resumption continuation,
which an aborting handler never invokes.

```talk
effect 'bail(message: String) -> Never

func work() {
	let owned = ["heap", "strings"]   // droppable buffer + elements
	'bail("stop")                     // suspended here; never resumed
}

func main() {
	@handle 'bail { message in print("caught: " + message) }
	work()                            // owned's drop never runs
}
```

**Shape 2 — intervening frames.** A frame between the performer and the
installer is suspended at an ordinary call; its owned locals' drops sit in
the code after that call, which never runs. The VM pops the frame without
looking at it (`interp.rs:273-279`).

```talk
func middle() {
	let held = ["intervening"]
	work()                            // suspends here; frame discarded
	print(held.count)                 // never reached — held leaks
}
```

**Shape 3 — the installing frame's own pre-`@handle` locals.** The
delimiter is `raw_ret_k`, the *raw* machine return — deliberately below
the drop wrappers layered onto `ret_k`/`tail_k` (`src/lower/mod.rs:229-234`).
An abort therefore exits the installing function without running even the
installing frame's own scope-exit drops.

```talk
func run() {
	let before = ["pre-handle"]       // owned before the install
	@handle 'bail { m in print(m) }
	work()
	print(before.count)               // abort skips before's drop
}
```

Two aggravations ride the same path: `'heap` **region releases** are
scope-exit obligations like any other (`RegionRelease` in the drop walk,
`src/lower/statements.rs:358`), so a region acquired in a discarded frame
is never released; and an abort **through a finalizer frame** — the
teardown pump's frames, `interp.rs:120-147` — abandons the finalizer's
remaining frees: the discard loop merely decrements the `finalizer_frames`
counter (`interp.rs:276-278`) and throws the half-finished teardown away.

The evaluator leaks identically for the same structural reason in
different clothes: it is a definitional CPS interpreter
(`src/lambda_g/eval.rs`) where the abandoned resumption is a closure that
becomes garbage — the drop code inside it never executes, and
`live_allocations()` reports the imbalance.

The invariant being violated is the project's central one — every owned
allocation freed exactly once per path — and the fix must respect the
architecture rule that already governs every other drop: **flow decides,
lowering emits, the runtime executes** (`src/flow/drops.rs` header,
ADR 0010, ADR 0017). The runtime holds no drop authority: it does not know
types, deinit hooks, witness dispatch, or region rules.

## Decision

Abort becomes a **discontinue-style unwind**, in OCaml's sense: a captured
continuation is consumed exactly once, by resuming (`continue`) or by
unwinding through its cleanup (`discontinue`) — never by silent discard.
Talk already has all the per-frame cleanup code (every function's
scope-exit drop machinery); the change is to make the abort path run it.

Concretely: the VM, instead of discarding the suspended frames, enters
each one *one final time* at an **unwind entry** — a block the lowerer
emits containing that suspension point's scope-exit drops — then pops it
and continues to the next frame, down to and including the installing
frame, and only then delivers the handler's value through the delimiter.
The finalizer-frame case falls out: a finalizer's frame unwinds through
its own remaining obligations like any other frame.

The runtime gains **control-steering only**: a pc table per chunk and an
unwind cursor. All cleanup *content* stays lowerer-emitted λ_G, produced
from flow-published drop candidates — no second drop authority.

### Unwind entries are per suspension site, not per function

A frame suspended mid-abort is stopped at a **capability-passing call
site**: either a perform (the capability application,
`lower_capped_perform`, `src/lower/effects.rs:336-371`) or an ordinary
call whose callee row carries user effects (the caller threads
capabilities into it — `lower_call`). This set is statically known to the
lowerer: it is exactly the calls where it appends capability arguments.
Row typing makes it complete — a callee that could transitively perform
(including through a closure argument) carries the effect in its row, or
the program did not typecheck.

At each such site where owned locals are live across the call, the lowerer
emits one unwind entry: a λ_G function `λ((), ⊥)`-shaped like the existing
`drop_scope` wrappers (`wrap_cont_with_following_drops`,
`src/lower/mir_lowering.rs:817-841`), whose body is the scope-exit drops
for the locals live at that point — built by the existing
`lower_candidate_drop_then` (`mir_lowering.rs:897-913`), so deinit-hook
dispatch, structural teardown, `RegionRelease`, and drop-flag guards are
the same code paths normal drops use — terminated by a new ⊥-typed
`Op::UnwindDone` (semantics below).

**Which locals: flow publishes, lowering reads.** The flow pass emits a
new candidate reason at each capability-passing MIR `Call`/`Perform`
statement — `DropReason::Unwind`, alongside the existing
`ScopeExit`/`EarlyExit`/`AssignmentReplace`/`TemporaryEnd`
(`src/flow/drops.rs`) — covering every owned local whose storage is live
across that statement, classified with the same
`Static`/`Dead`/`Conditional`/`Open` elaborations. Lowering builds the
entry from the candidates exactly as `lower_early_exit_then` builds an
early-exit edge (`mir_lowering.rs:1674-1696`), with the drop-stack
remainder fallback explicitly **not** replicated (per M2, that fallback is
slated for deletion; the new path starts single-authority).

**Per-site entries versus one per-function entry consulting flags — we
choose per-site.** The alternative reading of "one unwind entry per
function, drop flags decide what is live" fails on two counts:

1. *Suspension points are call sites, not perform sites.* An intervening
   frame is suspended at an ordinary effectful call. One shared entry
   cannot know which call the frame stopped at, so every droppable local
   in every effectful function would need a dynamic initializedness flag
   maintained on the **non-abort** path — writes at every init, move, and
   drop, paid whether or not an abort ever happens. That violates the
   fast-path requirement below.
2. *Precedent.* rustc gives every MIR `Call` terminator its own `unwind`
   edge into cleanup blocks specific to that program point, and LLVM
   `invoke`s each carry their own landing pad — per-site static tables,
   zero instructions on the happy path, cost only in code size. That is
   the shape that earned the name "zero-cost unwinding".

Drop flags are not displaced — they move *inside* the sites. A local whose
initializedness at a given suspension site is path-dependent gets a
`Conditional` elaboration there and its entry consults the existing
runtime flag, exactly as statement-position drops do
(`lower_dynamic_assignment_drop_then`). Flags are assignment-converted
cells (`Op::CellNew`, `src/lower/statements.rs:757`), and cells live in
the machine's slot arena outside the frames (`interp.rs` header), so
unwind code reads them without any new plumbing.

**Encoding: structural, not a side map.** The unwind entry rides the call
expression itself — the λ_G application terminal gains an optional unwind
operand (a `Func` reference). It must be structural because every λ_G
pass has to see it: `fv.rs` must count its captures for closure
conversion, `subst.rs` must rewrite it during β-specialization
(Eqs. 14-18), `check.rs` must type it, `print.rs` must render it, and the
scheduler must reach it. A `Program`-level side table would be invisible
to substitution and re-create the NodeID-side-map failure mode the
pipeline just finished deleting.

### VM mechanics

- **`Chunk` gains an unwind table**: `(suspension_pc, entry_pc)` pairs
  (today a chunk is name/code/arity/n_regs,
  `talk-runtime/src/lib.rs:313-318`; `bytecode.rs` grows the encoding).
  The scheduler populates it when emitting a `Call`/`CallIndirect` whose
  λ_G application carries an unwind entry: the entry is a non-escaping
  continuation uniquely referenced by this chunk, so it schedules as a
  block of the same chunk by the existing block rules, and the table maps
  the pc *after* the call insn (which is what a suspended frame's `pc`
  holds — the interpreter advances `pc` before executing, `interp.rs:158`)
  to the entry block's pc.
- **Abort compiles explicitly.** The lowerer emits abort as a dedicated
  form (`Op::Abort(delimiter, value)`) instead of a bare-value computed
  application. The scheduler compiles it to `CallCont` as today — and
  deletes the shape-sniffing "computed callee applied to a non-tuple"
  heuristic at `schedule.rs:326-331` — and the evaluator gains a hook it
  can recognize (below).
- **`CallCont` becomes "begin unwind".** The one-shot identity check runs
  first, unchanged (`Cont(frame_index, frame_id)` validation,
  `interp.rs:265-269`): a dead delimiter still traps before anything
  unwinds. Then, instead of the discard loop, the machine records
  `unwinding = { target, value }`, pops the aborting handler's own frame
  immediately (its locals' drops already ran on its normal path *to* the
  abort — the handler body's `ret_k` is the delimiter, so body lowering
  emits its scope-exit drops before the tail), and enters the loop:
  - top frame index > target: look up the frame's `pc` in its chunk's
    unwind table. Hit → set `pc` to the entry and resume normal
    execution: the drop code runs *in that frame*, referencing its
    registers, and may make real calls (deinit hooks, finalizer pumps) —
    those push frames above the cursor and return normally. Miss →
    nothing owned is live there; pop and continue.
  - `Insn::UnwindRet` (the compilation of `Op::UnwindDone`) executed by
    the cursor frame: pop it, continue the loop.
  - top frame index == target: same lookup — **this is where the
    installing frame's pre-`@handle` locals drop**, because its
    suspension pc is a capability-passing call inside the handled extent
    and its `Unwind` candidates there include everything live, installed
    before or after the `@handle`. After its entry completes, pop it and
    deliver the stashed value to its caller's dest register — the
    unchanged tail of today's `CallCont` (`interp.rs:280-288`).
- **Finalizer frames** run their unwind entries like any frame; the
  `finalizer_frames` counter decrements at the pop points exactly where
  the discard loop decrements it today (`interp.rs:276-278`), only now
  *after* the frame's cleanup ran, so the teardown pump's "don't advance
  while a finalizer runs" invariant (`interp.rs:114-121`) is preserved
  through the unwind.
- **Drop order** is innermost-frame-first (performer → installer), and
  within a frame reverse declaration order — the same order the drops
  would have run had each function returned normally. Region releases
  ride the candidates in that order (ledger rule F unchanged).

### One-shot identity, resumed-then-aborted, nested depths

The `Cont(frame_index, frame_id)` protocol is untouched. Unwinding
consumes the delimiter exactly as discard did: the target frame pops, so
any second use of the same `Cont` fails the identity check. A handler
that resumes (`continue v` = the capability returning — zero new cost)
and whose extent later performs again suspends at *fresh* pcs; because the
table is keyed by dynamic pc, the second abort's unwind reflects the
current live sets with no staleness, no per-perform bookkeeping.

Nested handlers aborting to different depths need nothing: the target is
whichever delimiter `Cont` the aborting handler captured, and the unwind
covers exactly the frames above it. An inner handler's installing frame
is, from an outer abort's point of view, an ordinary intervening frame —
its extent's locals drop via its own suspension-site entry. Capability
templates and materialization (`materialize_cap`,
`src/lower/effects.rs:172-256`) are unchanged.

### Aborts during unwind

Unwind-entry code cannot itself perform a user effect directly: drop glue
calls deinit hooks through a fixed signature with no capability
parameters, so an effectful deinit body cannot be reached from a drop (it
would have failed typing at the conformance). The one indirect route is a
`RegionRelease` inside an entry pumping a finalizer whose body performs —
finalizers capture their capabilities lexically at creation (ADR 0011),
so this is possible when the creating extent is still live. v1 rule: a
`CallCont` while `unwinding` is `Some` **traps** ("abort during abort
unwinding") — the precedent is Rust aborting the process on
panic-during-unwind. Lifting this to nested unwinds is future work and is
flagged as an open question below.

### Evaluator parity

The evaluator has no frames to steer: it β-reduces
(`src/lambda_g/subst.rs`), the delimiter is — after substitution — just
the installing activation's `k` closure, and the abandoned resumption is
unreachable garbage. Frames cannot be recovered from closures, so the
evaluator interprets the *same lowered annotations* dynamically:

- A machine-level **extent stack**. Evaluating an application that
  carries an unwind entry pushes `(k, u)` — the call's continuation value
  (the argument tuple's last item) and the evaluated unwind-entry value.
  Every application compares the applied label against the **top** entry
  only; a match pops it (the call completed normally, or resumed). LIFO
  suffices: in one-shot CPS the innermost suspended call's continuation
  is always the next of the recorded ones to run.
- `Op::HandleInstall(delimiter)`, emitted at each `@handle`
  (`lower_mir_handling`, `src/lower/mir_lowering.rs:1292-1346`), pushes a
  **delimiter marker**; the scheduler compiles it to *nothing* (the VM
  needs no marker — the `Cont`'s frame index is the marker). The marker
  pops when its delimiter is applied, normally or by abort.
- `Op::Abort(delimiter, v)`: pop entries top-down, applying each unwind
  entry as a nested evaluation with a distinguished done-continuation —
  precisely the existing `run_finalizer` pattern
  (`src/lambda_g/eval.rs:133-152`), with `Op::UnwindDone` terminating the
  nested run the way `finalizer_done` does — until this delimiter's
  marker; pop the marker; apply the delimiter to `v`.
- **Label identity** is sound because β-reduction mints fresh labels for
  every activation-dependent function (`subst.rs` Eqs. 17-18): a
  continuation that closes over the activation's values — any with live
  droppables — is per-activation unique. A capture-free continuation
  label shared across recursive activations is still resolved correctly
  by the LIFO discipline. A recursion-under-handler abort test pins this.

The cost is a label comparison per application, in the reference engine
only — the engine whose entire purpose is to be the slow, honest spec
(`src/vm/README.md`).

### The non-abort fast path costs zero (on the VM)

- **Resume** is the capability's `Ret` — not one instruction changes.
- **Effectful calls that never abort** execute identically: the unwind
  table is static chunk metadata consulted only inside `CallCont`'s
  unwind loop. No flags are written for unwinding's sake (flags exist
  only where flow already needed `Conditional` drops), no closures are
  allocated, no parameters are threaded. The cost is code size — one drop
  block per capability-passing call site with live owned locals — and
  table bytes, the same trade rustc's landing-pad tables make.
- The evaluator pays its comparison; the VM, the engine with performance
  claims, pays only on abort.

## Rejected alternatives

**VM-side per-frame drop tables, interpreted at unwind time** — the
runtime walks a table of (register, type/teardown-kind) pairs per frame
and frees accordingly. Rejected on the no-second-authority principle:
"lowering emits, runtime executes" is the contract every other drop in
the system honors (`src/flow/drops.rs`, ADR 0010, ADR 0017), and the
review's M2 finding documents what happens when two authorities answer
one drop question. The runtime would need type knowledge it deliberately
lacks — user deinit hooks and their recursion guards, existential witness
dispatch, structural teardown, region ledger rules — a drifting
re-implementation of `lower_drop_value_then` inside `interp.rs`. Every
future drop-semantics change would then land twice.

**Double-barrelled CPS** (Thielecke): thread an unwind continuation
parameter through every effectful function; each suspension site passes
`λv. site drops; caller_uk(v)`; abort applies the perform site's `uk`.
Semantically clean and engine-uniform — the unwind chain is ordinary
lowered code, and the VM needs no changes at all — but it pays on the
fast path: an extra parameter in every effectful signature and call, and
a closure *allocation* at every suspension site with live droppables,
abort or not. It also re-grows exactly the calling-convention surface
ADR 0011 deleted (`normal_k`/`abort_ok` and friends). Kept in the record
because it is the natural fallback if the evaluator's extent stack proves
unsound in practice.

**Abort as a sentinel return value**: effectful calls return
value-or-abort; each post-call point branches, runs its drops, and
re-returns the sentinel. This *is* the pre-ADR-0011 abort-capable calling
convention, deliberately deleted (handler-site-dependent signatures, a
branch on every effectful return). Not relitigated.

**OCaml's documented fallback — GC finalizers on dropped continuations**:
needs a GC to notice the drop; Talk's ownership discipline exists to not
need one, and OCaml's own manual recommends explicit exactly-once
consumption over the finalizer path ("the runtime cost of finalisers is
much more than the cost of capturing a continuation").

## Consequences

- The three leak shapes, the region-release skip, and the
  finalizer-abandonment case all close; abort-heavy programs leave the
  container-leak fence (discharging the debt bullet in ADR 0011's
  consequences, which should be annotated when this lands).
- **Observable semantics change**: user `Deinit` hooks and finalizers now
  run on abort paths where they were silently skipped. Programs that
  accidentally relied on abort-as-leak will see new side effects — this
  is the fix working.
- New surface, all small: an optional unwind operand on λ_G application
  terminals (with `check.rs`/`fv.rs`/`subst.rs`/`print.rs` support);
  `Op::UnwindDone`, `Op::Abort`, `Op::HandleInstall`;
  `Insn::UnwindRet`; the `Chunk` unwind table and its `bytecode.rs`
  encoding; machine `unwinding` state; the evaluator's extent stack.
- Unwind entries remain ordinary lowerer-emitted cleanup over the same
  artifact, but the current free-balance verifier intentionally ignores
  unwind operands and `Op::Abort`; abort-only paths are not independently
  verified.
- Multi-shot resumption remains out of scope; one-shot enforcement is
  unchanged.
- v1 limitations, accepted: abort-during-unwind traps; `@handle` inside a
  nested block remains unsupported at the `lower_handle_statement` /
  `nested_handle` fence, independent of this ADR.

## Implemented regression coverage (both engines where executable, balance asserted)

1. **Performer's frame**: shape 1 above — owned array in the performing
   function; abort; `live_allocations()`/`live_count()` zero.
2. **Intervening frame**: shape 2 — owned array in a frame between
   performer and installer; abort; balanced.
3. **Installing frame**: shape 3 — owned locals declared before the
   `@handle`; abort; balanced.
4. **`'heap` across an abort**: a region-allocated object live across the
   perform; abort; region released (rule F), `live_objects()` zero,
   finalizer side effects observed.
5. **Abort during a finalizer**: a finalizer body performs; its handler
   aborts; the finalizer's remaining frees run; teardown completes;
   balanced.
6. **Resumed paths unchanged**: the existing handler corpus
   (`tests/programs/{handlers,caller_locals_handler,nested_handlers,
   resume_across_frames,multi_effect_handlers}.tlk`) passes byte-identical.
7. **Nested depths**: inner and outer handlers over the same extent, each
   aborted in turn; locals of the inner extent drop exactly once per
   abort.
8. **Resumed-then-aborted**: a handler resumes once, the extent performs
   again, the handler aborts; live sets at the second suspension are the
   ones dropped.
9. **Recursion under a handler**: an abort out of a recursive performer
   (pins the evaluator's label-identity/LIFO discipline).
10. **Function-value calls (R9/F-B)**: an owned local remains live across
    an indirect effectful call; abort; the indirect application's unwind
    entry releases it on both engines.
11. **Witness applications**: structural lowering tests require a
    MIR-published entry on witness dispatch and a no-entry control when
    no owned cleanup is live. End-to-end effectful witness coverage remains
    blocked by the existing effect-requirement typing limitation.
12. **Owned suspension operands (F-C)**: concatenated String, direct Array,
    direct `'heap`, and object-only aggregate operands are materialized before
    performs and suspension-capable ordinary calls. Their allocation/region
    ownership is released on resume or abort on both engines.

## Citations (per decision)

- **Abort must consume the continuation through its cleanup
  (discontinue), not discard it**: OCaml requires every captured
  continuation be resumed "either with a `continue` or `discontinue`
  exactly once"; `discontinue k e` exists precisely so the suspended
  stack unwinds through its cleanup, and GC-finalizer unwinding is
  documented as the costly fallback, not the design.
  [OCaml manual: Effect handlers](https://ocaml.org/manual/5.5/effects.html)
  (verified 2026-07-11: "every captured continuation must be resumed
  either with a continue or discontinue exactly once"; "it is recommended
  that the user take care of resuming the continuation exactly once
  rather than relying on the finaliser");
  [Sivaramakrishnan et al., Retrofitting Effect Handlers onto OCaml, PLDI 2021](https://arxiv.org/pdf/2104.00250).
- **Per-call-site cleanup blocks reached only on unwind, selected by
  static tables (zero-cost on the non-unwind path)**: rustc's MIR gives
  `Call` terminators their own unwind edges into cleanup blocks and
  elaborates drops there with maybe-init precision (`Static`/`Dead`/
  `Conditional`/`Open` — the categories Talk's `DropElaboration` already
  mirrors, per ADR 0010); LLVM's `invoke`/landing-pad model is the
  per-site precedent underneath.
  [rustc-dev-guide: drop elaboration](https://rustc-dev-guide.rust-lang.org/mir/drop-elaboration.html),
  [rustc `TerminatorKind::Call` unwind edges](https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/mir/syntax/enum.TerminatorKind.html).
- **Handlers that don't resume run finalization during unwinding**:
  Koka's `initially`/`finally` clauses run resource cleanup when an
  operation aborts instead of resuming — finalization is a
  language-level obligation of non-resumption, not a GC afterthought.
  [Koka book §3.4.11, "Initially and Finally"](https://koka-lang.github.io/koka/doc/book.html).
- **Cancelling a suspended continuation by running its cleanup is the
  standard shape in newer designs**: WasmFX's `resume_throw` injects an
  exception into the suspended continuation so it unwinds through its
  handlers rather than being dropped.
  [Phipps-Costin et al., Continuing WebAssembly with Effect Handlers, OOPSLA 2023](https://arxiv.org/pdf/2308.08347).
- **Rejected double-barrelled alternative**: Thielecke, *Comparing
  Control Constructs by Double-Barrelled CPS*, HOSC 2002 (already the
  abort-only citation in ADR 0011).
- **One-shot frame slices and the existing `CallCont`**: Hieb, Dybvig &
  Bruggeman, PLDI 1990 (per ADR 0011 and the `interp.rs` header).

**Novel composition (flagged per convention, no direct prior art):**
discontinue-style unwinding realized as *lowerer-emitted, per-suspension-
site unwind entries* addressed by a chunk pc table and populated from the
flow pass's liveness/drop-candidate machinery — rustc's landing pads
unwind exceptions in a stack-walking native runtime, and OCaml's
discontinue re-raises into ML exception frames, whereas here the "landing
pads" are ordinary λ_G continuations steered by a one-shot delimited
`CallCont` in a CPS-scheduled VM, with drop *content* owned entirely by
the compiler. The evaluator-side reading of the same annotations as a
dynamic extent stack (markers at `@handle`, entries at suspension sites,
`run_finalizer`-style nested evaluation of entries) is likewise novel and
exists to keep the two engines executing one artifact.
