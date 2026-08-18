# 0067 - Direct-style concurrency

Status: accepted, implemented

## Context

ADRs 0050 and 0058-0063 built a complete concurrency stack on polling:
futures as hand-written state machines, a wake-driven executor, wakers,
and registration discipline for channels and timers. ADRs 0064/0065 made
that surface redundant. With first-class one-shot resumptions, waiting is an
effect: the handler holds the continuation and execution later resumes where
it stopped.

## Decision

1. **Core exposes intent-named waiting effects.**

   ```talk
   pub effect 'yield() -> ()
   pub effect 'recv<static N: Int>(channels: [Int; N]) -> ()
   pub effect 'send(handle: Int) -> ()
   pub effect 'wait_until(deadline: Instant) -> ()
   ```

   `recv` waits until any listed channel has a value or closes. Its static
   argument keeps the source handle list inline; ADR 0035 monomorphizes each
   reachable operation and handler clause. `wait_until` carries a core
   monotonic `Instant`, and runtime deadline registration uses nanoseconds.

   `core/Host.tlk` installs blocking fallbacks that register each interest,
   block the worker through the ADR 0059/0063 runtime operation, unregister,
   and continue. A cooperative scheduler is a nearer handler for the same
   effects. Dynamic nearest-handler routing remains the only dispatch.

2. **The direct surface replaces futures.** `Receiver.recv()` returns `T?`
   directly, bounded `send` returns `Bool`, `sleep(Duration)` returns after an
   absolute monotonic deadline, and `select_recv(a, b)` waits with
   `'recv(channels: [a.handle, b.handle])`. The same effect supports any
   statically-sized handle list; there is no separate two-channel operation.

   Deleted surface: `Poll`, `Waker`, `Context`, `WakeSet`, `Future`,
   `join_all`, `block_on`, `Recv`, `SendFuture`, `Sleep`, and `Select2`.
   Channel endpoint lifecycle guards and `Either` remain.

3. **The cooperative scheduler uses the Step-knot without mutable clause
   captures.** `yield` is both the public cooperative yield and the blocking
   host's immediate no-op fallback. `spawn` remains the task creation effect.
   A receive handler specializes over its inline input, copies the handles
   into the scheduler's dynamic task state only when the task actually
   suspends, and stores the one-shot resumption beside them. The scheduler
   probes waiting tasks, resumes ready tasks, and, when none can progress,
   registers every interest and blocks through the runtime.

4. **Parallel workers keep their existing structure.** `parallel_run` moves
   each Send-checked job to a worker, installs the same `io`, `alloc`,
   `yield`, `panic`, `recv`, `send`, and `wait_until` fallbacks there, and
   joins in order. `run_blocking` remains available when code using the raw
   task primitives needs to install that worker context explicitly.

5. **The cut is clean.** Keeping a second future executor would duplicate
   every invariant. Delivery order, close-to-`none`, bounded backpressure,
   timer composition, and leak accounting are expressed and tested directly.

## Consequences

- Async code is straight-line code; effect rows state `recv`, `send`,
  `wait_until`, and `yield` rather than exposing the parking mechanism.
- Receive waiting is N-ary without allocation on the blocking path. The
  cooperative path materializes handles only as scheduler state after a task
  suspends.
- `Duration` and `Instant` are core monotonic primitives. Deadline arithmetic
  and runtime registration preserve nanoseconds end to end. Hosts whose wait
  primitive is coarser may wake late, never early.
- Cooperative and parallel execution still compose through the runtime's
  registration and wake layer.

## Validation

1. Ordered delivery, close-to-`none`, dropped-receiver cleanup, bounded
   backpressure, sleep-at-least, and left-biased select hold on VM and C.
2. The root scheduler interleaves spawned tasks over `'yield`, channels, and
   sleeps on one worker.
3. One generic `recv` handler accepts one, two, and more inline handles with
   concrete layouts on VM and C.
4. Sub-millisecond deadlines retain nanosecond values through the Talk, VM,
   and native runtime layers.

## Relationship to existing decisions

- **ADR 0035:** static effect operation identities and clauses monomorphize.
- **ADR 0064/0065/0068:** one-shot resumptions and clause-derived suspension
  provide the scheduler mechanism.
- **ADR 0059/0062/0063:** queues, reservation, registration, wake, and
  deadline machinery remain the runtime layer.
- **ADR 0039:** host fallbacks are ordinary handlers; no effect is
  compiler-privileged.
