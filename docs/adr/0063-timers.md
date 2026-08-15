# 0063 - Timers

Status: accepted (implemented 2026-08-08 — monotonic clock and deadline
registration ops in VM and native; the park operation takes the earliest
registered deadline as its timeout; stdlib `sleep`; corpus pin
tests/programs/timers.tlk)

## Context

ADR 0059 fixed the shape of asynchronous waiting: a wake source is
anything that registers against a parked task. Channels were the first
source; a timer is the second, and the first whose wake comes from time
rather than another worker. What was missing: a clock the runtimes agree
on, a registration with a deadline, and a park that sleeps *until* the
earliest deadline instead of indefinitely.

## Decision

1. **`sleep(ms)` is a lazy future in stdlib `task`.** Constructing it does
   no work (ADR 0050); the deadline anchors at the FIRST poll. Poll
   compares the monotonic clock against the deadline: past it, `ready`
   (with the requested duration, a deterministic output); otherwise it
   registers the deadline once and returns pending. Drop before
   completion unregisters, `DropToken`-gated (ADR 0060).

2. **Deadlines are worker-local registrations, like channel waits.** The
   count of "reasons to park" a worker reports to its executor is channel
   waits plus deadlines, so the executor's park rule is unchanged. The
   park operation computes the earliest registered deadline and waits
   with that timeout — a timed wake is just another broadcast-shaped
   readiness hint, and the woken executor re-polls everything (spurious
   wakes stay legal).

3. **The clock is monotonic milliseconds from an arbitrary per-process
   anchor**, exposed as a control op: `CLOCK_MONOTONIC` in the native
   runtime, a process-start `Instant` in the VM, `Date.now` on wasm
   (wall-clock, the best a browser offers; sleeps care about deltas).
   Wall-clock time and calendars are host-effect territory (ADR 0039),
   not this.

4. **Single-threaded wasm busy-waits.** On the no-atomics VM path, a park
   with a registered deadline spins until the earliest deadline passes —
   a blocking sleep on a single thread IS a blocked thread. Parks with no
   deadline keep the deadlock report.

## Consequences

- Everything rides `chan_ctl` (now, register-deadline, unregister): no
  new instructions, no bytecode change, no executor change.
- `select2(recv, sleep)` is the timeout pattern, for free (ADR 0061).
- Timer resolution is the park timeout's resolution; there is no timer
  wheel — registration lists are executor-sized, and scans are per park.
- IO readiness remains open and is explicitly NOT prejudged here; it
  needs an async host-IO design first, and would arrive as one more wake
  source in this same shape.

## Validation

1. `block_on(sleep(ms))` takes at least `ms` of monotonic time (corpus,
   all backends).
2. `select2(recv, sleep)` times out on a quiet channel and resolves to
   the data side when a worker sends well inside the timeout (corpus).
3. A sleeping worker parks with a timeout rather than spinning (the
   corpus programs complete in bounded wall time on every backend).

## Relationship to existing decisions

- **ADR 0059:** the second wake source, through the same registration
  and check-then-park protocol.
- **ADR 0061:** composes into timeouts.
- **ADR 0050/0060:** lazy construction; exactly-once cancellation.
