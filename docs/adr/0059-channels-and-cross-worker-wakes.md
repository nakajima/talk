# 0059 - Channels and cross-worker wakes

Status: accepted (implemented 2026-08-08 — `chan_send`/`chan_take`/`chan_ctl`
inline IR through MIR, bytecode (opcodes 67–69), VM, C, and LLVM; stdlib
`channel`/`Sender`/`Receiver`/`Recv` over rc-guarded lifecycle tokens; the
local executor parks on outstanding external registrations with a
check-queue-then-park protocol in both runtimes; corpus pin
tests/programs/parallel_channels.tlk. Threads-WASM validated in headless
Chrome — wasm/test-threads.sh runs the parallel corpus, channels included, on
Web-Worker-backed threads over shared wasm memory against the native pins.)

## Context

ADR 0050 gave Talk lazy futures, wakers with coalescing wake laws, and
checked `Send`/`Sync` transfer capabilities. ADR 0058 gave it structured
parallel scopes over a pooled native runtime and isolated VM workers,
with a help-joining pool that keeps nested scopes deadlock-free. Both
deliberately deferred one thing: no operation yet makes one task wait on
another *worker*. Wakers hold `'heap` state, so the type system itself
confines every wake to the worker that minted it, and the local
executor treats a poll round that wakes nothing as a deadlock — correct
while self-wakes are the only wake source.

Channels change that. A receiver parks until a sender — possibly on
another OS thread — provides a value, which forces four designs at
once: a waker representation that crosses threads, a park operation
that replaces the deadlock panic when external wakes are pending, a
value hand-off between workers, and a discipline that keeps the wake
laws (coalescing, no lost wakes, safe late wakes) true under real
concurrency. ADR 0058 already specified the check-queue-then-park
protocol and required it be written once and cited by both runtimes.

## Decision

1. **The first channel is a multi-producer, single-consumer transfer
   channel**, surfaced in stdlib `task` (names provisional):

   ```text
   channel<T>() -> (Sender<T>, Receiver<T>)     where T: Send
   Sender.send(consume value: T) -> ()           never blocks (unbounded)
   Receiver.recv() -> RecvFuture<T>              a lazy future
   RecvFuture.poll -> Ready(T?) | Pending        none = every sender gone
   ```

   `Sender` is `Send` (clonable, one per producing task); `Receiver` is
   `Send` but not clonable. Bounded channels and `select` are follow-up
   decisions; select in particular requires the lost-wake proof for
   losing waiters that ADR 0050 demanded and nothing here prejudges.

2. **The channel is a runtime object, not a Talk value.** Its queue
   holds transferred values — shared-heap moves on native, transfer
   packets on the VM — behind the same handle discipline as tasks:
   runtime-minted, generation-checked, never decodable from program
   bytes. Talk-level `Sender`/`Receiver` wrap the handle; their drops
   release it, and the last release frees the queue.

3. **Cross-worker wakes reuse the pool's own signal.** A parked
   receiver registers `(scope, task)` with the channel; `send` marks
   that task woken under the pool lock and broadcasts the same
   condition variable joins already wait on. No second wake mechanism
   exists: ADR 0058's check-queue-then-park protocol gains one more
   "queue" to check (pending wakes for the parked worker), and the
   proof obligation stays singular.

4. **The local executor learns to park instead of panic.** A poll
   round that polls nothing is a deadlock only when no task holds a
   live external registration (a pending recv). With registrations
   outstanding, the executor parks on the runtime and re-drains its
   wake set when signalled; the deadlock report remains for the
   genuinely wakeless case. The pure-Talk wake set is untouched —
   external wakes arrive as task indices through a runtime drain
   operation merged into the same coalescing drain the executor
   already runs.

5. **Waker laws extend unchanged.** A channel wake is a readiness
   hint; spurious wakes stay permitted (a racing consumer may drain
   the value first — `recv` re-polls and re-parks); wakes for
   completed or cancelled tasks drop at drain; a `RecvFuture` dropped
   before completion unregisters, and a wake racing that cancellation
   is harmless.

6. **Sequential targets get the same semantics.** On single-threaded
   hosts, send-then-park cannot make progress across threads, so park
   with a nonempty ready set simply runs the woken task inline —
   ADR 0058's spawn-site policy extended to waits. A program that
   deadlocks sequentially (recv with no live sender-holding task)
   reports the deadlock exactly as today.

## Consequences

- Finalized MIR gains channel host operations (create, send, recv
  registration/attempt, handle release) and one park/drain pair —
  value-operand operations in the ADR 0058 mold, lowered per target,
  validated in bytecode.
- The native pool's lock/condvar pair becomes the single
  synchronization point for joins, helps, and wakes; its protocol
  comment becomes the normative text both runtimes cite.
- The VM's isolate model holds: channel values cross by packet, so a
  cyclic or capability-carrying payload is refused at send exactly as
  at spawn.
- `parallel_join_all` is unaffected; programs combining scopes and
  channels get pipelines (producers in one scope feeding a consumer
  task) without detached tasks — handles still never escape.
- Timers, IO readiness, and `select` become expressible follow-ups:
  each is "a wake source registering against a parked task", the shape
  this ADR fixes.

## Validation

1. A consumer task receives, in order, values sent by producer tasks on
   other workers; the same program is valid and identical in output on
   the sequential reference paths.
2. Send-after-receiver-drop and recv-after-all-senders-drop resolve
   (no-op / `none`), never trap or hang.
3. A wake racing a park is never lost (stress, both runtimes, ADR 0058
   validation item 10's lanes).
4. Non-`Send` payloads reject at compile time; capability-carrying
   payloads reject at the packet boundary on the VM.
5. Dropped `RecvFuture`s unregister: a subsequent send neither wakes a
   dead task nor leaks the value (it stays in the queue for the next
   receiver or frees with the channel).
6. The executor still reports genuine deadlock (no live senders, no
   registrations) rather than parking forever.

## Relationship to existing decisions

- **ADR 0050:** implements the deferred "trusted synchronization
  operations" over the Future/waker laws without changing them.
- **ADR 0058:** consumes its park protocol and pool signal; keeps
  structured scopes as the only task surface.
- **ADR 0044/0045:** channel queues live in the runtime, outside the
  managed value model; values enter and leave by the transfer rules.
