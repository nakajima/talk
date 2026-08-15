# 0065 - Native suspension by resumable functions

Status: accepted, implemented on the C target (phase 2 of ADR 0064).
The LLVM backend was retired rather than brought to parity (ADR 0066).

## Context

ADR 0064 gave the VM first-class one-shot resumptions and left the
native targets failing closed at the seam. Lifting that requires
capturing a native extent — every activation between a suspending
perform and its installer — and re-entering it later. Native stacks
cannot be sliced portably; something must change about how suspending
code compiles.

Two families were considered. **Fibers** (side stacks, switched at
suspension) keep the emitters untouched but demand OS context-switch
machinery, per-extent stack sizing, and a MIR-level outlining transform
to give each extent an entry point — a pass with real ownership hazards
across the outline boundary. **Resumable functions** (state-machine
lowering) keep MIR untouched and concentrate the work at the MIR→target
seam, which is where this codebase already concentrates such work: the
abort protocol is a return-status convention with per-call-site checks
the emitters generate today. Suspension is the same shape with a second
status. Fibers are the rejected alternative.

The decisive facts:

- **MIR functions are flat CFGs over an explicit locals array.** The C
  emitter already compiles every function as `TalkValue l[N]` plus
  labeled blocks. Moving `l` into a heap frame saves *all* state by
  construction — a suspension point stores one resume-label id. No
  liveness analysis exists because there is nothing to decide.
- **The abort machinery is the template.** `talk_abort_to` sets
  thread-locals and returns; every call site checks `talk_unwinding`
  and runs an emitted cleanup block. Suspension adds a sibling status
  with a save-and-return stub, and cancellation *reuses the emitted
  cleanup blocks unchanged*.

## Decision

1. **Which functions compile resumable is a backend fact, computed by a
   call-graph fixpoint over the finalized module.** Seeds: functions
   containing `Inst::Suspend`. Propagation: direct calls to a marked
   function mark the caller; if any address-taken (`MakeClosure`)
   function is marked, functions containing `CallIndirect` are marked.
   Propagation runs all the way up (it does not stop at installers —
   position-aware cutoffs are a later precision win, not a correctness
   need). No frontend bit, no MIR metadata, no new instructions: the
   set is derivable from `Suspend` sites alone, because an effect no
   one performs suspends nothing. The helper lives beside
   `needs_identity` in talk-native-runtime's shared emission support.

2. **Resumable form, externally invisible.** A marked function keeps
   its C signature. Internally it splits into a wrapper (allocate the
   heap frame, store arguments, enter) and an impl over the frame
   (`TalkValue *l = fr->l;` — instruction emission is unchanged) whose
   entry dispatches on `fr->rpc`. Marked functions enter the shadow
   stack with a *frame-owned identity* that survives suspension and
   re-entry.

3. **Two kinds of suspension point, both mechanical.**
   - An `Inst::Suspend` site resolves its handler (the same
     nearest-live-entry search performs use), allocates the resumption
     slot and segment record, stashes the arguments, stores its rpc,
     sets the pending status, and returns.
   - A call to a possibly-suspending callee is followed by a pending
     check: store rpc, link the callee's frame as `fr->child`, publish
     this frame as the pending child, return. The dispatch's re-entry
     case re-invokes the child and rejoins the same post-call path.

4. **The installer's call-site stub is where suspensions land, and the
   clause runs on the native return path.** When the pending status
   reaches the frame whose identity matches the suspension's target
   entry, the stub roots the segment with its own frame, captures the
   handler entries at or above it, opens the search floor, calls the
   clause with the stashed arguments plus the slot — and *returns the
   clause's result*. On first suspension the native caller is the
   original chain, so clause-return is abort; on re-suspension the
   frame was re-entered by `talk_resume`, so the same return delivers
   the clause result as `resume`'s answer. One code path, both
   semantics — the ADR 0064 invariant that the clause takes the
   installer's continuation, realized by ordinary `return`.

5. **`resume` and `cancel` are plain calls that drive re-entry.**
   `talk_resume(slot, v)` takes the segment (one-shot trap on a spent
   slot), re-installs its handler entries under the root frame's
   unchanged identity, publishes the resume value, and re-enters the
   root impl; emitted case-paths recurse to the deepest frame, whose
   suspend-site resume path reads the value and continues. A
   re-suspension targeting the re-installed entry is handled entirely
   inside that re-entry by the root's own stub. `talk_cancel(slot)`
   re-enters the root in cancel mode: the deepest suspend site jumps to
   its own unwind edge (the release planner gives `Suspend` one, like
   any call), and every parent's *existing* unwind check unwinds it in
   turn — ADR 0027's cleanup emission is the cancellation machinery.

6. **One documented divergence, fail-closed.** A suspension that
   propagates *past* a resumption boundary — a resumed extent
   performing a suspending effect whose handler lies below the
   `resume()` call — traps on native ("a suspension crossed a
   resumption boundary on this target (not supported yet)"). Effect
   rows do not mark `resume()` callers, so no static set can soundly
   include them; the VM supports the pattern, the ledger records the
   difference, and lifting it is future work (a cooperating
   `talk_resume` chain node).

## Consequences

- Non-suspending programs compile byte-for-byte as before; marked
  functions pay one heap allocation per activation and one status
  check per call site — the price of being suspendable, paid only by
  code that is.
- ADR 0049's elimination, the abort path, rows, and the VM are
  untouched. No bytecode changes; the wire format is already complete.
- The ADR 0064 reference programs are promoted to `tests/programs`
  with parity pins, making suspension a VM ↔ C invariant the sweeps
  enforce permanently — and phase 3 (the direct-style scheduler
  surface) unblocks.

## Validation

1. The three ADR 0064 corpus programs (generator roundtrip,
   cancel-releases, stepper interleave) produce their pinned output on
   the C target, exactly as on the VM — including the exit-time leak
   accounting proving cancel releases owned values through the emitted
   cleanup blocks.
2. Deep re-suspension across resume generations exercises re-entry,
   entry re-installation, and identity stability (the stepper program).
3. The crossing rule traps with its message rather than corrupting the
   chain.

## Relationship to existing decisions

- **ADR 0064:** implements its phase 2 exactly as scoped; semantics
  unchanged, one recorded native divergence.
- **ADR 0027:** the return-status protocol and per-site cleanup blocks
  are reused for propagation and cancellation.
- **ADR 0037/0038:** the work sits at the target seam; nothing is
  re-derived that typing decides — the marked set is a *backend*
  approximation that is sound by construction, not a semantic fact.
- **ADR 0049:** unaffected; suspend sites already count as handler
  uses.
