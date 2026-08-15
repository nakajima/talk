# 0067 - Direct-style concurrency

Status: accepted, implemented (phase 3 of ADR 0064 — the poll/future
stack is retired; direct-style channels, bounded sends, sleep, select,
`run_blocking`, `parallel_run`, and the `coop` scheduler are the
surface, on the VM and the C target alike)

## Context

ADRs 0050 and 0058–0063 built a complete concurrency stack on polling:
futures as hand-written state machines, a wake-driven executor, wakers
with coalescing laws, registration discipline for channels and timers.
It works on every target — and ADR 0064/0065 made it redundant. With
first-class one-shot resumptions on the VM and the C target, waiting is
a suspending effect: the operation that would have returned `Pending`
performs, the handler holds `k`, and control returns exactly where it
left off. Every hard law of the poll stack existed to compensate for
stateless re-entry; stateful re-entry needs none of them.

The design was validated by spikes before this ADR: closures created
outside a handler extent perform suspending effects inside it
(invocation-scoped rows), linear resumptions ride arrays through enum
payloads, and `-> () 'suspending` parses (the lexeme `suspending` is
reserved in bare row positions).

## Decision

1. **Waiting is a family of monomorphic suspending effects, declared in
   core and given blocking host fallbacks.** The scheduler never
   touches values — *park-then-take*: an operation parks until its
   source is ready, then the resumed, fully-typed code takes:

   ```talk
   pub effect 'park_recv(handle: Int) -> () 'suspending
   pub effect 'park_send(handle: Int) -> () 'suspending
   pub effect 'park_sleep(deadline_ms: Int) -> () 'suspending
   pub effect 'park_recv2(a: Int, b: Int) -> () 'suspending
   ```

   `core/Host.tlk` installs root fallbacks whose clauses block the
   worker through the existing ADR 0059/0063 runtime ops
   (register → park → unregister) and immediately resume — so channel
   and timer code works with no scheduler at all, on the main thread
   and inside spawned workers, exactly as today. A cooperative
   scheduler is just a nearer handler for the same effects. No
   flags, no introspection: dynamic nearest-handler routing is the
   dispatch.

2. **The blocking surface replaces the future surface.** `recv()`
   returns `T?` directly, looping status → take → park. Bounded `send`
   returns `Bool` directly, looping liveness → reserve-and-send → park.
   `sleep(ms)` returns when the deadline passes. `select_recv(a, b)`
   returns `Either<T?, U?>` with the old left bias, parking on both
   handles via `'park_recv2`. Deleted outright: `Poll`, `Waker`,
   `Context`, `WakeSet`, `Future`, `join_all`, `block_on`, `Recv`,
   `SendFuture`, `Sleep`, `Select2`, the wake-set plumbing, and the
   wake-law corpus. `Either` survives. The channel endpoint types and
   their ADR 0060 lifecycle guards survive unchanged. The runtime gains
   one op: a non-reserving room probe, so a scheduler can test
   readiness without claiming the reservation the resumed sender will
   claim itself.

3. **The cooperative scheduler is a stdlib module (`coop`) built on the
   Step-knot, with no mutable clause captures.** Two more effects,
   `'pause() -> () 'suspending` (cooperative yield) and
   `'spawn_task(task: Task) -> () 'suspending`, plus:

   ```talk
   enum TaskStep {
       case finished
       case wants_recv(Int, Resumption<(), TaskStep>)
       case wants_send(Int, Resumption<(), TaskStep>)
       case wants_either(Int, Int, Resumption<(), TaskStep>)
       case sleeping(Int, Resumption<(), TaskStep>)
       case paused(Resumption<(), TaskStep>)
       case spawned(Task, Resumption<(), TaskStep>)
   }
   ```

   `drive(task)` installs one pure clause per effect — each returns its
   `TaskStep` — and `coop::run(main)` owns the queues: resume what is
   ready (probing with the same status ops), requeue pauses, push
   spawns, and when everything waits, fall back to the runtime's
   blocking park with every parked interest registered — which is what
   makes cooperative tasks and cross-worker channels compose: the
   scheduler is one registered waiter among workers. All state flows
   through answer values; a known VM bug with clauses mutating captured
   arrays is thereby never on the path.

4. **Parallelism keeps its shape, minus the futures.** Workers are
   closures; `parallel_run(jobs, worker)` spawns one Send-checked
   worker per job and joins in order. Worker entries (and the new
   `run_blocking` helper that replaces the hand-written preamble in
   corpus programs) install the ambient fallbacks — io, alloc,
   yield_now, panic, and the park family — so a worker's channel and
   timer calls block its thread, as before.

5. **The cut is clean.** Nothing external consumes the future surface;
   keeping two executors alive would double every invariant. The
   behavioral pins — delivery order, close→`none`, backpressure bounds,
   timeout composition, leak accounting — are re-expressed in direct
   style with identical outputs wherever semantics allow, and the
   corpus programs that existed only to exercise the executor's wake
   laws retire with it.

## Consequences

- Async user code is straight-line code. The state-machine tax, the
  registration flags, and the `DropToken` dances on waiting futures
  are gone; the endpoint lifecycle guards remain.
- Effect rows now surface waiting honestly: a function that may park
  carries `'park_recv` (etc.) in its row, and the C target's resumable
  set — hence the heap-frame cost — tracks exactly the call paths that
  can wait.
- The scheduler composes with worker parallelism through the same
  runtime park/wake layer channels always used; nothing about
  ADR 0058/0059's cross-worker story changes.
- `select` generalizes later by widening the park family (or a
  variadic park); this ADR ships the two-way race the old surface had.

## Validation

1. Every surviving behavioral pin from ADRs 0059–0063 holds in direct
   style on VM and C: ordered delivery, close→`none`,
   dropped-receiver frees, bounded backpressure with parked senders,
   sleep-at-least, two-way select with left bias and unclaimed-value
   retention.
2. A `coop::run` program interleaves spawned tasks over `'pause`,
   channels, and sleeps deterministically, single-worker (corpus, both
   targets).
3. A cooperative consumer receives from a producer on another worker —
   the scheduler's blocking fallback path (corpus, both targets).

## Relationship to existing decisions

- **ADR 0064/0065:** the consumers this capability was built for.
- **ADR 0059/0062/0063:** their runtime layers (queues, reservation,
  registration, park/wake, deadlines) are retained verbatim; only the
  Talk-level waiting surface changes.
- **ADR 0039:** the park fallbacks are ordinary `#handle` rows in
  `_with_host`; no effect is compiler-privileged.
- **ADR 0050:** superseded at the surface level; its memory-model
  groundwork (Send/Sync, transfer) is untouched.
