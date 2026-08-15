# 0064 - First-class one-shot resumptions

Status: accepted; phase 1 (VM) and phase 2 (native, via ADR 0065's
resumable-function lowering on the C target) implemented. The LLVM
backend was retired instead of brought to parity (ADR 0066).

## Context

ADR 0011's control model compiles `'continue` as the clause returning to
the perform site, and ADR 0050 deliberately preserved that: "the
perform-site continuation cannot be stored." The poll-based executor
built on that restriction works — but everything hard about it exists
*because* polling is stateless re-entry: the wake-coalescing laws, the
registration/unregistration discipline, the lost-wake analysis, and the
hand-written state machine every async computation must become. A
handler that can store the suspended computation and resume it later
replaces that whole apparatus with "hold `k`, resume `k`" — generators,
control inversion, and single-worker schedulers become ordinary
handlers. ADR 0050 named the missing pieces: answer-typed perform-site
continuations, linear continuation storage, a stack representation, and
borrow-across-suspension rules. This ADR supplies them.

## Decision

1. **Suspension is declared on the effect, not discovered at the
   handler**: `pub effect 'pause() -> () 'suspending`. Perform sites of
   a suspending effect compile to a distinct suspend operation, every
   handler for it must bind the resumption, and the effect-row machinery
   is untouched — a suspending effect joins and discharges rows exactly
   like any other, and no effect name is compiler-privileged (ADR 0039
   holds). The declaration marker is also what phase 2's row-directed
   native lowering will key on. Phase 1 restrictions, rejected at
   check time: suspending effects take no type generics and no `mut`
   arguments.

2. **The clause binds the resumption as an ordinary linear value.** A
   handler for a suspending effect names one binder per payload plus a
   final binder for the resumption:

   ```talk
   #handle 'pause { k in ... }
   #handle 'emit { value, k in ... }
   ```

   `k`'s type is `Resumption<R, A>` — `R` the effect's declared return
   (what resuming supplies to the perform site), `A` the handled
   extent's answer (the installing function's return type, exactly the
   type an aborting clause already produces). `Resumption` is a plain
   `'linear` core struct wrapping a worker-local slot: linearity gives
   static exactly-once (it must be consumed, cannot be duplicated or
   silently dropped), the slot table gives a dynamic trap as backstop,
   and linear declarations never derive `Send`, so a resumption cannot
   cross a worker — the handler-boundary rule needs no new enforcement.

3. **`resume` and `cancel` are core functions, not syntax**:

   ```talk
   resume<R, A>(consume k: Resumption<R, A>, value: R) -> A
   cancel<R, A>(consume k: Resumption<R, A>) -> ()
   ```

   `resume` delivers `value` to the suspended perform site and runs the
   extent to its next suspension or completion; its return value is the
   extent's answer either way. `cancel` discards the extent, unwinding
   every captured frame through the same per-frame cleanup entries an
   effect abort already uses (ADR 0027) — cancellation cannot leak.
   `'continue` is rejected inside a suspending clause: the binder
   replaces it.

4. **The captured segment includes the installing frame, and the clause
   takes its place.** At a suspending perform, the frames from the
   `#handle`-installing frame through the perform site — the entire
   delimited extent, the installer's own remaining block included — move
   off the stack into the resumption. The clause frame is pushed at the
   installer's position with the installer's outward linkage, which
   makes the semantics fall out of frame discipline alone:

   - a clause that completes without consuming `k` in a resuming path
     simply *returns*, delivering its value where the installing
     function would have returned — the existing abort typing, no
     delimiter machinery;
   - `resume(k, v)` splices the segment above the resumer and rewires
     the segment's base to the resume call site, so the extent's
     completion arrives as `resume`'s return value like any call's;
   - the handler entry itself travels inside the segment and re-installs
     at the resume site, so a re-suspension captures up to the *new*
     base and its clause returns to the *resumer* — deep-handler
     semantics at every generation, with the one-shot caveat inherent to
     dynamic-extent systems: a resumed extent sees the handlers live at
     the resume site, not a snapshot of its birthplace.

5. **Borrows do not cross the segment boundary.** The segment's root is
   the installing frame, so a reference to data outside the extent can
   only enter through the installer's own borrowed parameters —
   everything deeper borrows from frames that travel with the segment.
   The checker therefore rejects a suspending `#handle` in a function
   with borrowed parameters: conservative, fail-closed, and aligned
   with the worker convention (task and generator bodies take `consume`
   arguments). Phase 2 owns the precise rule.

6. **Native support is phase 2's resumable-function lowering
   (ADR 0065).** The C target compiles the functions a suspension can
   propagate through in heap-framed, re-enterable form; pure code keeps
   the native stack and ADR 0049's elimination. ADR 0049's absence
   proof is taught that a suspend operation uses its effect's handlers
   (its routing does not go through `FindHandler`). The LLVM backend
   was retired rather than brought to parity (ADR 0066).

## Consequences

- Generators, inverted control, and cooperative single-worker
  scheduling are expressible as ordinary handlers today, on the VM,
  with no new statement forms — two core functions and one declaration
  attribute.
- The poll/future stack (ADRs 0050, 0058–0063) is unchanged and remains
  the cross-target, cross-worker story until phase 2 reaches parity;
  this ADR adds a control capability, it does not migrate anything yet.
  Phase 3 — rebuilding task/channels/select/timers as a scheduler
  handler and retiring the wake-law machinery — is its own decision
  once native parity exists.
- One new MIR operation family (suspend/resume/cancel), three bytecode
  opcodes, no bytecode format bump, no changes to rows, `FindHandler`,
  or the abort path.

## Validation

1. tests/reference/effects/suspending_generator_roundtrip.tlk — `'emit`
   values arrive in order across resume generations, and the extent's
   completion value flows back through the whole resume tower.
2. tests/reference/effects/suspending_stepper_interleaves.tlk — two
   extents park simultaneously as `Step.parked(k)` values and finish
   later, each resumed outside any handler; the recursive answer type
   (`Step` carrying `Resumption<Int, Step>`) is legal because a
   resumption stores only its slot.
3. tests/reference/effects/suspending_cancel_releases.tlk — `cancel`
   releases a buffer owned across the suspension through the captured
   frame's cleanup entry (the suspend site carries an unwind edge the
   release planner fills, exactly like a call's); the VM exit balance
   proves it.
4. talk_tests::suspending_handlers_enforce_their_static_rules — double
   resume is a moved value, an unconsumed resumption is a linearity
   error, `'continue` in a suspending clause gets its dedicated
   diagnostic, the binder count includes the resumption, and a
   suspending `#handle` under borrowed parameters rejects.
5. c_backend_tests::suspending_handlers_reject_on_the_c_target — the C
   seam fails closed; the LLVM seam shares the same pre-pass.

Known phase-1 sharp edges, deliberate: each resume-inside-a-clause
generation deepens the stack (the frame budget bounds it; the stepper
pattern above is the flat alternative); a resumed extent sees the
handlers live at the resume site; the linearity diagnostic renders the
`Resumption` name as `<type>` (cosmetic namer gap).

## Relationship to existing decisions

- **ADR 0011/0027/0031:** the call-based clause protocol, the floor
  discipline, and abort unwinding are all preserved for non-suspending
  effects; suspension reuses the unwind tables for cancellation.
- **ADR 0039:** no privileged effect names; the marker is declared,
  uniform, and row-visible.
- **ADR 0049:** the elimination pass learns suspend sites as handler
  uses.
- **ADR 0050:** implements the extension it scoped out, without
  disturbing what it built.
- **ADR 0053 (Deinit × sharing):** irrelevant here by construction —
  linearity exempts resumptions from implicit sharing entirely.
