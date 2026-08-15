# 0058 - Scoped parallel tasks and per-target worker isolation

Status: proposed; implemented for the sequential-reference and native
targets — `task_spawn`/`task_join`/`task_width` host operations through
finalized MIR, bytecode (format 8), VM, C, and LLVM; the structured
`parallel_join_all` surface in stdlib `task` over a capture-free
argument-passing worker convention (closures capture effect capabilities
at creation, so `_run_worker` installs the root fallbacks by direct
`#handle` statements before any effectful closure exists); `Send`
enforcement at the spawn boundary; and OS-thread workers in the native
runtime (pthread per task, spawn-site fallback), measured at >6x CPU
utilization on eight CPU-bound tasks (7.5x after the pool landed). The
native runtime now runs a persistent width-capped pool with HELP-BASED
joining — a joiner runs queued tasks instead of sleeping — which
balances uneven tasks and keeps nested scopes deadlock-free (corpus:
tests/programs/parallel_nested.tlk); `parallel_join_all` spawns each
future as its own task. The VM's isolate workers are
implemented too: each task runs on its own OS thread over a fresh
machine sharing the module, values cross through transfer packets
(buffer interiors interpreted via the element kind their typed stores
recorded; sharing inside the transferred tree preserved by retains; the
parent's copies released at spawn), worker IO buffers and replays at
join, worker exit balances are enforced, and the copier structurally
refuses cells, `'heap` handles, continuations, cyclic or mixed-kind
buffers — so a closure carrying frame-bound handler capabilities cannot
cross, exactly the handler-boundary rule, enforced against untrusted
bytecode. Measured >6x CPU utilization on the VM as well; wasm32 without
shared-memory atomics keeps the spawn-site sequential path, and wasm32
WITH atomics takes the threaded path on Web-Worker-backed threads
(`wasm_thread`), validated in headless Chrome by wasm/test-threads.sh
against the native corpus pins (wasm/tests/parallel.rs — every worker
is a child of the main thread, which must stay unblocked to relay
spawns, so the harness runs each program inside one worker from an
async main-thread test). The wake-queue/parking operations are
deferred until a cross-worker wake source (channels, timers) exists —
today wakers contain `'heap` state, so the type system itself confines
every wake to its worker.

## Context

ADR 0050 fixed the asynchronous groundwork: lazy futures advanced by polling,
executor-owned tasks, checked `Send`/`Sync` transfer capabilities, and one
semantic contract across the VM, C, LLVM, and WASM targets. It deliberately
left three things open: the task spawn/join surface, the task-handle policy
(what dropping a handle means), and how each target physically executes
tasks in parallel.

The groundwork it demanded now exists. The type system derives and checks
`Send`/`Sync` structurally. The native runtime has atomic managed-buffer
owner transitions (Arc-discipline orderings, measured under 1% uncontended)
and worker-local (`_Thread_local`) frame, handler, unwind, arena, and stack
state, so any OS thread can execute generated code as an independent worker.
The VM's interpreter state is a per-worker `Worker` struct over the shared
immutable `Module`. The wake-driven local executor (stdlib `task`) runs the
same futures on every target.

What remains is the parallel half, and its hardest question is the VM. The
VM models buffers as offsets into one simulated byte memory with per-machine
allocation records, and its values use non-atomic reference counts. Making
that state safely shareable between threads would demand unsafe concurrent
access to a growable byte arena, atomic allocation records, and an atomic or
dual-representation value type — a large body of unsafe code in the one
component whose purpose is to be the obviously-correct oracle the native
backends are differentially tested against.

## Decision

1. The first parallel surface is **structured**: a scope spawns a set of
   `Send` futures, runs them to completion on a worker pool, and returns
   every output before the scope's caller resumes. No detached tasks and no
   first-class task handles exist in this ADR.
2. Spawning is an ownership sink gated by the checked capabilities: each
   spawned future must be `Send`, and each output crossing back must be
   `Send`. The boundary reads the type system's checked facts through
   finalized MIR; it infers nothing at runtime.
3. **Transfer of a `Send` value is representation-polymorphic per target.**
   Native targets move values over the shared heap's thread-safe owner
   transitions. The VM transfers by structural copy between isolated
   per-worker machines. Both implement the same source-visible contract:
   `Send` excludes every type with observable identity, and Talk values are
   value-semantic, so a structural copy is observationally equivalent to a
   move.
4. **The VM's parallel executor runs isolated workers.** One process, one
   shared immutable module, N machines: each worker owns a complete machine
   (byte memory, allocation records, regions, cells) plus its interpreter
   `Worker` state. Nothing inside a worker changes; no VM value becomes
   shareable between threads. Spawn copies the future in; join copies the
   output out; allocation balances are per-machine and each must reach zero
   when its worker retires.
5. **The native parallel executor runs shared-memory workers**: OS threads
   over the process heap, using the atomic owner transitions of ADR 0050
   and the worker-local runtime state already in place. Work stealing lives
   here, as runtime policy.
6. Scheduling policy is not semantics. The VM's reference scheduler may
   statically partition tasks across workers (a steal would be a deep copy);
   the native scheduler may steal. Correct programs cannot observe the
   difference, per ADR 0050's executor-policy rule.
7. **The scheduling loop is Talk source; the runtime supplies only the
   runtime.** A worker's life is an ordinary stdlib function
   (`_worker_main` in stdlib `task`, name provisional): it installs the
   root host fallbacks, then loops — take the next woken task, poll it
   through its witness, record completion or re-queue. What source cannot
   express stays in the runtime, and under the reference static
   partitioning it is exactly four operations: transferring the spawned
   `Send` futures to their workers, enqueuing a cross-worker wake,
   draining this worker's wakes with parked waiting (the only blocking
   primitive), and the scope's join barrier with output transfer back.
   Everything else — per-task queued/alive flags, coalescing, outputs
   accounting — is worker-local Talk data, so ADR 0050's task scheduling
   state (idle, queued, running, complete; a wake racing an active poll
   re-queues) is realized by the wake queue plus worker-local flags with
   the claim-before-poll rule, not by a separate runtime state machine.
   Every target runs the same Talk scheduling logic over its own
   target's transfer discipline — shared-memory moves on native, isolate copies on the VM —
   so the scheduler itself is covered by differential testing, and
   scheduling policy stays visible in source rather than buried per
   backend (ADR 0039's discipline applied to executors). The one protocol
   implemented per target, check-queue-then-park, must be written down
   once and cited by both implementations: a lost wake there is the one
   per-target divergence the shared scheduler cannot mask.
8. Finalized MIR gains **task host operations** — spawn-set construction
   and transfer, next-woken-task acquisition (parking), cross-worker
   wake, and join-barrier output transfer — with value operands,
   alongside (not replacing) the scalar `io` operation table. A task entry
   carries its future's poll and drop witnesses as ordinary operands
   through the existing dictionary machinery; polling from a worker is an
   ordinary witness call under the fixed `mut`-receiver writeback
   convention. The operations name no source API and no executor policy
   (ADR 0047's seam discipline). Bytecode gains matching opcodes and
   validation rules.
9. **Parallel wakers are runtime handles.** A cross-worker wake must be
   invokable from any worker thread, so the parallel executor's context
   lends a runtime-backed waker (opaque, generation-checked, safe after
   completion) that routes through the runtime wake queue. The local
   executor's pure-Talk wakers are unchanged; which representation a poll
   receives is the executor's choice and invisible to the future.
10. Every worker executes futures under the same source-owned root host
    fallbacks the program entry installs (ADR 0039): `_worker_main` opens
    with the same wrapper discipline as `_with_host`, so a task observes
    the ambient effects of the program, never another worker's
    frame-bound handlers (ADR 0050's handler-boundary rule).
11. All workers share one IO sink, serialized by the host. Interleaving of
    concurrent writes is unspecified; programs wanting deterministic output
    order must join before printing.
12. A `'panic` reaching a worker's root fallback terminates the process,
    exactly as it does on the main worker today. Recoverable task failure
    is a library concern over `Result` outputs, not an executor feature.

The provisional surface, following stdlib `task`'s local executor and
subject to the same naming caveat as ADR 0050:

```text
parallel_join_all(consume futures: [F]) -> [F.Output]
    where F: Future + Send, F.Output: Send
```

Programs valid on the parallel executor are valid on the local executor;
targets without threads (baseline WASM) run the same call sequentially.

## Why isolation is legitimate for the VM

The objection writes itself: ADR 0050 adopts Rust's shared-memory model, and
isolates do not share memory. The resolution is that ADR 0050's model is a
contract about *source-observable behavior*, and the checked capabilities
make the two implementations indistinguishable:

- A `Send` value contains no heap-object references, no cells, no closures,
  and no raw pointers — nothing whose identity a program can observe.
  Copying such a value and moving it produce the same results.
- Copy-on-write owner counts differ between the strategies (a copied buffer
  arrives unique; a moved one keeps its count), but counts are observable
  only through `_is_unique`, whose sole effect is whether a copy-on-write
  detach happens — a cost, never a result.
- `Sync` sharing across VM workers is realized as copy-on-read of the
  shared value. For identity-free types this is again equivalence, not
  approximation.

What isolation genuinely changes is *coverage*, not semantics: the VM
cannot exhibit cross-thread races on payload memory, because it has none.
Race detection for the shared-memory implementation therefore rests
entirely on the native stress and sanitizer lanes (ADR 0050 validation
item 17), and this ADR makes that shift explicit rather than accidental.

Future synchronization libraries (channels, locks) must be host-mediated
operations in the VM — a channel send copies through a runtime queue; a
lock checks its value out and in. Channels already have transfer semantics
by contract, so the reference implementation stays honest; the native
implementation may use real shared memory beneath the same operations.

## Structured first, handles later

Exposing task handles forces the question ADR 0050 documented as
executor-divergent in Rust: does dropping a handle cancel, detach, or
block? A structured scope dissolves the question — every child provably
completes (or the scope panics) before the scope returns, no handle
escapes, and cancellation remains what ADR 0050 already defined: dropping
an incomplete future before it is spawned. Strict-linear futures reject at
the spawn boundary exactly as they do at the local executor today, since
the scope drops still-pending futures only on the panic path — and a panic
terminates the process, which is the one exit strict linearity cannot
gate.

Detached tasks, handles, and select-style joining are follow-up decisions
that must be made against this scope primitive, not instead of it.

## Alternatives rejected

### A shared-memory VM

Rejected above all for trust. Sharing the simulated byte arena requires
unsafe concurrent access to a growable `Vec<u8>` (growth relocates every
buffer under concurrent readers), atomic allocation records, and an atomic
or dual-representation `Value`. It taxes the single-threaded path that
every differential test depends on, and a subtly racy reference
interpreter would poison the oracle role that justifies the VM's
existence.

### One OS process per VM worker

Rejected. Isolation at the machine level already provides the memory
independence; processes would add serialization of the module, slow
spawn/join by orders of magnitude, and complicate IO and lifecycle for no
semantic gain.

### First-class task handles in the first surface

Rejected here, per the section above. The handle-drop policy deserves its
own decision after the structured scope exists and real use cases surface.

### The scheduling loop in the runtime

Rejected. A runtime-owned executor loop would put scheduling policy where
source cannot see it, require the VM and the native runtime to each
reimplement the same loop, and make every policy change a per-backend
runtime edit. With the loop in stdlib Talk, one scheduler drives every
target, differential tests cover it, and the runtime's surface shrinks to
threads, queues, parking, and transfer — things source genuinely cannot
express.

### Implementing VM spawn over the scalar `io` operation table

Rejected. The `io` table carries integer triples; spawn and join move
typed values between machines and must be visible to bytecode validation.
Widening the io convention to smuggle values through integers would
reintroduce exactly the forgeable-handle shape ADR 0050 forbids.

### Deep-copy transfer on native targets too

Rejected. Native code holds real pointers into one heap; the atomic owner
transitions are already paid for, moves are O(1), and the native executor
is the performance story. Uniform copying would surrender the entire
benefit of the shared-memory model where it is real.

## Consequences

- The VM gains parallelism with no new `unsafe`, no atomic value counts,
  and zero overhead for programs that never spawn.
- Spawn, join, and (VM-only) steal are O(size of the transferred value);
  the reference scheduler avoids stealing, and the transfer copier can
  build on the existing transitive value walk used by the exit-balance
  footprint.
- The differential-testing story narrows for race bugs: VM-vs-native
  agreement checks results, while data-race coverage lives in native
  sanitizer lanes. Parallel corpus programs must produce
  join-order-deterministic output.
- Because the scheduling loop is shared Talk source, VM-vs-native
  agreement covers the scheduler itself; only the runtime operations
  (threads, queues, parking, transfer) have per-target implementations,
  and only they need target-specific stress lanes.
- The implementation order falls out of the split: task host operations in
  MIR, the native runtime primitives (pool, wake queue, parking), the stdlib
  `_worker_main` loop, then the VM runtime reusing the same worker-main
  over isolate transfer.
- Library artifacts (ADR 0048) keep their serialized-invocation contract;
  their global teardown lists are not thread-safe, so a library invocation
  running a parallel scope must either take the native executor's workers
  from the runtime it embeds or remain on the local executor until the
  library lifecycle learns about workers. This is a known gap, recorded
  here.
- The parallel waker's runtime representation must coexist with the local
  executor's pure-Talk wakers behind one `Context` surface; the mechanism
  (representation switch inside core's waker, or executor-specific context
  construction) is an implementation choice inside core, not a new
  contract.
- Bytecode validation (ADR 0050 item 16) becomes concrete: task opcodes
  validate operand shapes, spawn sets reference only chunks whose
  transferred layouts satisfy the published `Send` facts, and wake handles
  are runtime-minted, never decodable from program bytes.

## Validation

1. The same parallel corpus programs produce identical, pinned output on
   the VM (isolated workers), C, and LLVM (shared-memory workers), and on
   the local executor (ADR 0050 items 10 and 15 for native).
2. Non-`Send` futures and non-`Send` outputs reject at the spawn boundary
   at compile time; the same futures run on the local executor (ADR 0050
   item 8).
3. A future transferred into a VM worker observes no shared identity:
   mutating a copied-in value never affects the parent's copy, matching
   value semantics on native.
4. Cross-worker wakes: a future polled on worker A whose waker fires from
   worker B is re-polled exactly once per coalesced wake set; wakes after
   completion are no-ops from any worker (ADR 0050 items 3–5 under
   parallelism).
5. Per-machine allocation balances hold: every VM worker retires at zero,
   and native exit balances hold under parallel scopes (ADR 0050 item 12
   extended).
6. Strict-linear futures reject at the parallel spawn boundary (ADR 0050
   item 7).
7. Native sanitizer/stress lanes exercise concurrent spawn/join, steal,
   and wake traffic; their absence is not replaced by VM tests (ADR 0050
   item 17).
8. Scope discipline: no program can observe a child task after its scope
   returns (no handle type exists to leak).
9. VM-vs-native agreement on parallel corpus programs exercises the shared
   `_worker_main` scheduling source on both runtimes; a scheduler bug
   cannot hide behind a per-target reimplementation.
10. The check-queue-then-park protocol is stress-tested for lost wakes on
    each runtime (native under the sanitizer lane, the VM under a Rust
    stress test): a wake enqueued concurrently with a worker's decision to
    park must always be observed.

## Research and precedent

- Rust `std::thread::scope` (RFC 3151): scoped threads with completion
  proven before the scope exits — the structured-join precedent.
- Trio's nurseries and Kotlin's structured concurrency: the argument that
  detached tasks and handle-drop policy should not be the primitive:
  <https://vorpus.org/blog/notes-on-structured-concurrency-or-go-statement-considered-harmful/>.
- JavaScript structured clone + workers, and Erlang/BEAM process heaps:
  isolate-per-worker with copy transfer as a correctness-first
  parallelism model.
- V8 isolates: one process, many independent heaps over shared immutable
  program data — the architecture the VM adopts.
- Blumofe & Leiserson (JACM 1999), Chase & Lev (SPAA 2005): the
  work-stealing lineage, native executor only, policy not semantics
  (carried over from ADR 0050).

## Relationship to existing decisions

- **ADR 0039:** workers enter Talk code under the same source-owned host
  fallbacks as the program entry; no compiler-known effects appear.
- **ADR 0044:** unchanged for the VM — per-worker machines mean the VM
  never shares mutable runtime state, so its memory model needs no atomic
  amendment. The native amendment made by ADR 0050 (atomic owner
  transitions) is what shared-memory workers run on.
- **ADR 0047:** finalized MIR remains the single seam; task host
  operations join it as target-neutral instructions with value operands.
- **ADR 0048:** library invocations remain serialized; parallel scopes
  inside library artifacts are deferred (see Consequences).
- **ADR 0050:** this ADR supplies the executor half 0050 deferred —
  structured spawn/join, per-target parallel execution, runtime wakers —
  without touching the Future contract, wake laws, or cancellation rule.
  The task-handle and detached-task policy remains open, now constrained
  to build atop the structured scope.
