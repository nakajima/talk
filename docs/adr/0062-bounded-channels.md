# 0062 - Bounded channels

Status: accepted (implemented 2026-08-08 — capacity through the create op,
reserve/register-send/unregister-send control ops in VM and native, take
broadcasts, direction-aware park; stdlib `channel_bounded`, `BoundedSender`,
`SendFuture`; corpus pin tests/programs/bounded_channel.tlk)

## Context

ADR 0059's channel is unbounded: `send` enqueues and returns. Backpressure
needs a send that waits for room — and inside an executor, "waits" must
mean a lazy future, never a blocked worker: a synchronous parking send
inside a poll would starve sibling tasks on the same worker (producer and
consumer sharing one executor would deadlock), violating the ADR 0050 poll
laws. The park machinery was built channel-scoped, not receive-scoped, so
sender-side waits reuse it; what parking lacked was a direction: a parked
receiver sleeps until "value or close", a parked sender until "room or
receiver gone".

## Decision

1. **Bounded creation mints a distinct sender type**:

   ```text
   channel_bounded<T>(capacity) -> (BoundedSender<T>, Receiver<T>)   where T: Send, capacity >= 1
   BoundedSender.send(consume value: T) -> SendFuture<T>              a lazy future, Output = Void
   BoundedSender.clone / drops                                        exactly as Sender (ADR 0060 token)
   ```

   The receiver side is the same `Receiver<T>`. The unbounded `Sender`
   keeps its immediate `send` — the two disciplines are different types,
   not a runtime mode of one method.

2. **Room is claimed by atomic reservation, not checked-then-raced.**
   A capacity-`n` channel tracks queued + reserved; the reserve op
   atomically takes a slot or refuses. `SendFuture.poll` reserves and
   sends in the same poll (no suspension between), so the bound is hard —
   racing senders cannot overfill. Sends to a dead receiver complete
   immediately and drop the value through typed glue (ADR 0059's rule).

3. **Sender parks are registered with a direction.** Register/unregister
   ops exist per direction; the park predicate re-checks, under the lock,
   readiness *per registration*: receive-waits wake on value/close,
   send-waits wake on room/receiver-death. `take` now broadcasts the same
   signal `send` and close always did — a consumer making room is a wake.

4. **A full-cycle stall is a hang, not a report.** The executor's genuine
   deadlock report still fires only when nothing is registered; tasks all
   parked on full queues with no consumer progress wait forever, like any
   system with backpressure. Detecting that requires global knowledge no
   runtime has.

## Consequences

- No new instructions, no bytecode format change: capacity rides the
  create op's spare operand, everything else is `chan_ctl` ops.
- The executor is untouched — parking was already "registrations exist,
  park on the runtime".
- `SendFuture` cancellation (drop before completion) unregisters via the
  ADR 0060 token gate; an owned-but-unsent value drops with the future.

## Validation

1. A capacity-1 sender parks and wakes as the cross-worker consumer
   makes room, delivering every value in order; a same-worker
   fill-then-drain alternation stays in bounds (corpus, all backends).
2. The C backend's exit-time leak accounting holds across all of it
   (corpus).
3. Send-to-dead-receiver completes and frees the value (corpus).
4. Non-`Send` payloads reject (`where T: Send`, same rule as ADR 0059).

## Relationship to existing decisions

- **ADR 0059:** reuses handles, transfer, check-then-park, close
  semantics; adds direction to registrations and a broadcast to `take`.
- **ADR 0060:** `BoundedSender`/`SendFuture` lifecycle guards.
- **ADR 0050:** send-as-future keeps the poll laws intact.
