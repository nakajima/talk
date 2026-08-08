# 0050 - Rust-style futures and data-race-free parallel execution

Status: proposed

## Context

Talk has typed algebraic effects, deep one-shot handlers, deterministic cleanup,
strict-linear nominal types, implicit-sharing value semantics, and several real
execution targets. It does not yet have an asynchronous execution or parallel
memory model.

The current `core/Async.tlk` is a sketch: it declares `Future`, `FuturePoll`,
`Context`, `Waker`, and a bare `'async() -> ()` effect. The host fallback in
`core/Host.tlk` resumes `'async` immediately because no scheduler exists. The
sketch does not define polling, wake coalescing, task ownership, cancellation,
worker migration, or cross-thread safety.

The existing runtime is synchronous:

- the VM has one active frame stack, handler stack, handler-search floor, and
  unwind state;
- the C backend uses the native C stack;
- the browser WASM surface calls the VM synchronously;
- managed-buffer owner counts and region external-root counts are non-atomic;
- function values resolve effects against the invoking task's dynamic handler
  stack (ADR 0051); handler clauses themselves contain delimiters naming their
  installing frames.

Talk's effects are not presently first-class coroutine continuations. A perform
finds and calls a handler clause; returning from the clause resumes the perform,
and finishing without `continue` discontinues to the handler delimiter. The
perform-site continuation cannot be stored. Reifying arbitrary stacks would be
a new control model, not an implementation of the current one.

Parallel execution is a first-order goal, not a possible later optimization.
The design must therefore distinguish asynchronous suspension from physical
parallelism, make worker transfer type-safe, and preserve one semantic contract
across the VM, C, LLVM, and WASM adapters.

There will be no `async` or `await` keyword and no compiler transformation that
turns direct-style functions into coroutine state machines. Surface names for
future construction, task spawning, joining, and communication are deliberately
outside this ADR. This ADR decides their semantic substrate.

## Decision

Talk adopts Rust's library-level concurrency model:

1. asynchronous computations are lazy `Future` values advanced by polling;
2. executors own tasks and poll only tasks whose wakers report possible
   progress;
3. a task is an executor-owned future plus scheduling and completion state;
4. local tasks may remain on one worker, while transferable tasks may migrate
   and execute in parallel;
5. `Send` and `Sync`-equivalent checked capabilities govern transfer and shared
   access across workers;
6. effects remain typed synchronous operations used by future implementations
   to request host behavior; an effect perform does not implicitly suspend an
   arbitrary Talk stack;
7. the shipped native executor is parallel and work-stealing, while executor
   policy is not part of source evaluation semantics.

This adopts Rust's `Future`/`Poll`/`Context`/`Waker` and `Send`/`Sync` contracts,
not Rust's async surface syntax, generator transformation, or one particular
runtime such as Tokio.

## Futures

A future is an ordinary Talk value with one associated output type and one poll
operation. The semantic signature is:

```text
poll(exclusive future state, Context) -> Poll<Output>

Poll<T>
  Ready(T)
  Pending
```

Exact source spelling is deferred. Polling obeys these laws:

1. `poll` never blocks the worker thread waiting for asynchronous progress.
2. `Ready(value)` completes the future and transfers ownership of `value` to
   the caller.
3. `Pending` leaves the future initialized and eligible for a later poll.
4. Before returning `Pending`, the future arranges for the current context's
   waker to be notified when another poll may make progress.
5. A wake is a readiness hint, not proof that the next poll will return
   `Ready`; spurious wakes are permitted.
6. Multiple wakes may coalesce into one queued poll.
7. An executor never polls one future concurrently and never polls it again
   after `Ready`.
8. A future may move between polls unless its type explicitly uses a separate
   stable-address facility.

The exclusive poll receiver is expressed with Talk's existing exclusive-borrow
and mutation rules. There is no `Pin` parameter in the base future contract.
Rust needs `Pin` because compiler-generated futures may contain self-references;
Talk adopts no such transformation, and safe Talk values cannot construct an
escaping self-reference. Address-sensitive future state requires a later
stable-address decision rather than an unconditional pinning layer.

Futures are lazy. Constructing one performs no asynchronous work unless its
ordinary constructor explicitly does work. An executor task makes a future
eager by taking ownership and polling it.

## Effects inside futures

Effects keep their current language semantics. A future's `poll` method may
perform effects named by its ordinary effect row. Core future implementations
use typed effects to make nonblocking host requests, inspect readiness, and
register the current waker. They then return `Ready` or `Pending` explicitly.

A handler cannot turn an arbitrary direct-style call stack into a pending
future. In particular:

- `continue` remains immediate one-shot resumption by returning from the clause;
- a clause cannot retain the hidden perform-site continuation;
- the current `MakeCont` remains a handler delimiter, not a task resumption;
- no compiler-known effect name implicitly changes the calling convention.

This preserves ADR 0039's single effect-routing mechanism and source-owned host
fallbacks. Core may replace the placeholder bare `'async` declaration and its
immediate fallback with typed readiness operations, but the compiler does not
name or privilege them.

First-class linear resumptions remain a coherent possible extension. Talk's
`'linear` declarations could enforce exactly-once resume or discontinue, but
that extension is not required for the Rust polling model and is not adopted by
this ADR.

## Context and wakers

A context lends the current task's opaque waker to a poll operation. A waker is
not an integer task ID and cannot be forged from source values.

A waker has these semantics:

- it may be cloned according to an explicit runtime ownership contract;
- it may be invoked from any host thread;
- waking schedules the associated task for a future poll and never polls it
  inline;
- waking a completed or cancelled task is a safe no-op;
- stale generations cannot wake a new task that reused storage;
- the runtime keeps the task alive for every live waker claim;
- releasing the final waker claim does not itself cancel a separately owned
  task.

The task's atomic scheduling state prevents concurrent polls and lost wakes.
At minimum it distinguishes running, idle, queued, and complete states and
records a wake racing with an active poll. Returning `Pending` after such a
race leaves the task queued.

## Tasks and executors

A task is executor state, not a second kind of source function. It owns:

- one future;
- its completion state and eventual output;
- atomic scheduling state;
- waker claims;
- executor-local accounting and cancellation state.

Executors may expose handles and scopes through ordinary core or library types,
but this ADR does not choose those APIs.

Two executor classes are semantic:

### Local executor

A local executor polls tasks only on their owning worker. Futures and outputs
need not be transferable. This is the fallback for types or hosts that cannot
cross worker boundaries.

### Parallel executor

A parallel executor may migrate a pending task between workers. Its future and
all state retained across a `Pending` return must be `Send`; any output moved to
another worker must also be `Send`. The future is still polled by at most one
worker at a time.

The reference native executor uses per-worker deques and work stealing. This is
a runtime policy, not a source guarantee about execution order, fairness, or
which worker observes a task. Correct programs cannot depend on poll count,
worker identity, or wake ordering unless a separate API explicitly exposes
such information.

The classical Blumofe-Leiserson work/span bound applies only to fully strict
fork-join computations. General channels, arbitrary task dependencies, and
external events remain valid but do not inherit that theorem. Documentation
and benchmarks must not claim the strict bound for a general task graph.

## `Send` and `Sync`

Talk adds two compiler-trusted marker capabilities with Rust's meanings:

```text
Send(T): an owned T may safely move to another worker
Sync(T): shared references to T may safely be used by multiple workers

Sync(T) iff Send(&T)
```

Exact source names may follow the Rust names. They are checked semantic
capabilities, not ordinary behavioral protocols that arbitrary safe source may
claim.

Conformance is structural by default:

- an aggregate is `Send` when every owned component is `Send` and its
  representation has a thread-safe transfer contract;
- an aggregate is `Sync` when every shared component is `Sync` and shared
  operations are data-race-free;
- `&T` is `Send` only when `T` is `Sync`;
- `&mut T` is `Send` only when `T` is `Send`, and the existing exclusivity
  checker proves no competing access;
- function values and futures derive the capabilities from their environments
  and retained state;
- a strict-linear type is not automatically `Send` or `Sync`;
- raw pointers, ordinary mutable cells, frame identities, handler delimiters,
  and thread-affine host handles are neither capability by default;
- host types receive capabilities only from their trusted import contract.

A user-defined unsafe conformance, if admitted later, must require the existing
`'unsafe` gate and becomes a proof obligation relied upon by MIR and the
runtime. Safe source cannot lie about either capability.

Parallel task creation is an ownership sink. MIR reads checked `Send`/`Sync`
facts; it does not infer thread safety from liveness, a debug name, or runtime
shape. A borrowed capture may enter an unscoped task only when its lifetime is
proven to outlive the task. A scoped executor may admit shorter borrows only
when every child is proven complete before the scope exits.

## Data-race freedom and memory representation

Safe Talk programs are data-race-free. Concurrent conflicting access without a
synchronization happens-before edge is rejected or made unrepresentable by the
`Send`/`Sync` boundary. Unsafe code that violates a trusted contract has the
same responsibility unsafe Rust has; target behavior follows the documented
atomic memory model rather than receiving a safe-language guarantee.

ADR 0044 currently places concurrent sharing and atomic owner counts outside
its model. This ADR amends that boundary on acceptance:

- a managed buffer advertised as `Send` uses thread-safe owner transitions;
- a region or closure environment advertised as transferable or shareable uses
  thread-safe external-root transitions;
- atomic ownership protects the ownership metadata only; it does not make a
  non-`Sync` payload safe to share;
- mutable heap objects with unrestricted aliases and ordinary shared cells are
  not `Sync` merely because their root counts are atomic;
- a representation with non-atomic ownership metadata cannot satisfy `Send` if
  independent owners may exist on different workers.

Talk retains ADR 0044's substrate-specific counts rather than introducing
uniform reference counting. Implementations may keep a distinct local and
atomic representation only when representation selection is fixed before the
value can publish and every call boundary preserves the selected contract.
There is no runtime promotion of a published local control block.

Core value-semantic buffers intended for ordinary cross-worker use, including
String and Array storage, must use thread-safe owner transitions. Their element
conditions remain structural: moving an array requires `Send(Element)`, and
sharing immutable access requires `Sync(Element)`. Copy-on-write mutation still
requires exclusive access to the owner and detaches before payload mutation;
atomic owner count changes do not authorize concurrent payload writes.

The concrete atomic operation vocabulary and memory-ordering API are a
follow-up Talk IR decision. Target adapters must map that vocabulary to the
Rust/C++20-style data-race-free memory model consistently; adapters may not use
plain loads and stores for operations declared atomic.

## Handler boundaries across tasks

A task does not inherit frame-bound dynamic handler installations from the
worker that created it. Handler clauses contain delimiters naming installing
frames; moving an installation would permit a task to abort across another
task's stack.

A future polled as a task executes under the executor worker's root host
handlers plus handlers installed by the future's own poll computation.
Invocation-scoped function effects resolve only against that task-local stack.
A future value is `Send` when its retained value environment is transferable;
function values carry no frame-bound handler capability.

Task-local handler inheritance, handler reinstallation, and handler-owner
routing are separate possible extensions. None is inferred from closure
creation.

## Cancellation and destruction

Rust cancellation occurs by dropping an incomplete future. Talk adopts that
future-level rule:

- destroying an incomplete affine future cancels it and runs ordinary
  deterministic cleanup for its initialized state;
- readiness registrations and waker claims owned by the future are released;
- a wake racing with cancellation is harmless;
- no future is polled after cancellation completes.

Strict-linear state cannot be cancelled by implicit destruction. A future that
contains a live strict-linear value is itself linear under Talk's existing
recursive grade rules. It must reach a consuming completion or an explicitly
defined consuming cancellation operation on every finite path. An unscoped
executor may reject such a future when it cannot prove that obligation.

Dropping a task handle is not defined here to mean cancellation or detachment.
Rust's language-level Future contract does not decide that policy; different
Rust executors choose differently. The task-handle and structured-scope ADR
must choose explicitly without changing the future cancellation rule above.

Talk's existing discontinue cleanup remains the effect-abort mechanism. Poll
cancellation does not synthesize a discontinue through a hidden perform-site
continuation because no such continuation exists in this model.

## Blocking operations

A poll operation may perform bounded computation but must not wait for external
progress while occupying an executor worker. Native blocking operations use a
separate bounded blocking pool or remain explicit synchronous calls whose use
can stall that worker. Arbitrary Talk futures are not moved to a foreign
blocking pool unless they satisfy the same `Send` contract.

CPU-bound work is parallelism, not asynchronous waiting. It may run as ordinary
transferable tasks on the parallel executor, subject to cooperative fairness:
a long poll monopolizes one worker until it returns. Preemption is not part of
the Future contract.

## Backend contract

Finalized MIR remains the single target seam under ADR 0047. It must represent
poll calls, checked transfer/share capabilities, task and waker host operations,
and atomic ownership transitions without naming a source API or executor
implementation.

### VM

The VM gains a shared machine substrate and multiple worker-local interpreter
states. Each worker polls one task at a time. Immutable module data is shared;
mutable runtime substrates follow their atomic or worker-local contracts.
Tasks contain future values, not detached VM call stacks.

### C and LLVM

Future implementations are ordinary finite Talk calls that return `Ready` or
`Pending`, so generated code continues to use the native stack. The native
runtime supplies the worker pool, task scheduling state, wakers, atomics, and
host reactor. No C stack copying, `setjmp` coroutine, `ucontext`, or implicit
CPS conversion is required.

### WASM

The Future contract is identical. Baseline single-threaded WASM executes the
same tasks on a local executor. A threads-enabled target may use shared memory,
WASM atomics, and workers for the parallel executor. Target capability affects
physical parallelism, not program validity or future semantics.

JavaScript host promises wake opaque Talk wakers and ask the executor to poll;
they do not resume a suspended Wasm stack. DOM- and JavaScript-affine operations
remain on their designated host worker.

## Communication and synchronization

The language adds no privileged channel, mutex, semaphore, or select construct
in this ADR. These are ordinary library/runtime types built over:

- `Future` and `Waker` for asynchronous waiting;
- `Send` and `Sync` for worker boundaries;
- trusted atomic and blocking synchronization operations;
- typed effects for host interaction.

Their exact contracts require separate decisions. In particular, a general
selection facility must define atomic registration and cancellation of losing
waiters; it is not approximated by polling every branch without a lost-wake
proof.

## Alternatives rejected

### Async/await syntax and automatic state-machine lowering

Rejected. Talk does not add dedicated keywords or transform direct-style
functions into hidden futures. Explicit ordinary types implement the Future
contract. This keeps suspension state visible to ownership and makes C/WASM
lowering ordinary control flow.

### First-class resumptions as the initial async substrate

Not adopted. Linear resumptions are compatible with Talk's strict-linear types
and algebraic-effect foundations, but they require exposing answer-typed
perform-site continuations, linear continuation storage, stack representation,
and new borrow-across-suspension rules. Rust's poll model achieves the selected
executor and parallelism goals without changing handler semantics.

### Runtime suspension of arbitrary Talk stacks

Rejected. It requires detachable VM frames and CPS or stack switching for C and
WASM, creating two control representations where explicit futures need one.

### OS thread per task

Rejected. It conflates logical concurrency with workers, does not scale to
large pending task sets, and prevents waker-driven multiplexing.

### A permanently single-threaded executor

Rejected as the reference runtime because parallelism is a primary goal. A
local executor remains required for non-`Send` tasks and targets without thread
support.

### Treat strict linearity as thread-transfer safety

Rejected. Exactly-once ownership does not prove that referenced payloads have
no aliases on another worker, that host handles are thread-independent, or that
internal ownership metadata is atomic.

### Make every type `Send` by atomizing counts

Rejected. Atomic ownership metadata protects counts, not payloads. Heap aliases,
cells, raw pointers, handler delimiters, and host-affine resources still need
structural rejection or synchronization.

### Executor-specific language semantics

Rejected. The language specifies Future, wake, transfer, sharing, and
cancellation laws. Work stealing, queue shapes, worker counts, and task-handle
policy belong to runtimes and libraries.

## Consequences

- Talk gains one async representation across every backend: explicit lazy
  futures.
- Parallelism is real on native and threads-enabled WASM targets while the same
  program remains valid on a local executor.
- Effects continue to provide typed host requests and user interception without
  becoming hidden stack suspension.
- User-authored asynchronous control flow uses ordinary explicit Future
  implementations; there is no privileged syntax transformation or generated
  state machine.
- `Send`/`Sync` become trusted semantic facts published by typing and consumed
  by MIR.
- Managed standard value types that cross workers pay for thread-safe ownership
  transitions; this cost must be measured, not wished away.
- Non-`Send` futures remain useful on local executors.
- Long-running polls can monopolize workers; cooperative task code must return
  to the executor.
- General communication, task-handle lifecycle, structured scopes, task
  failure, and source atomic APIs remain follow-up decisions constrained by
  this substrate.

## Validation

Acceptance requires tests and oracles for all of the following:

1. `Ready` transfers the output once and a completed future is never repolled.
2. `Pending` without a wake remains idle; waking requeues the task.
3. A wake racing with `Pending` is not lost.
4. Repeated wakes coalesce and never cause concurrent polls.
5. Wake after completion and wake after cancellation are safe no-ops.
6. Dropping an incomplete affine future releases every initialized resource.
7. A future containing strict-linear state cannot be silently cancelled.
8. Non-`Send` tasks reject at a parallel executor boundary and run on a local
   executor.
9. Structural `Send`/`Sync` derivation accepts and rejects nested aggregates,
   borrows, closures, futures, heap references, cells, raw pointers, and host
   handles correctly.
10. Multiple workers execute independent CPU-bound tasks concurrently on VM,
    C, and LLVM reference targets.
11. Work stealing never duplicates or loses a task and each future has at most
    one active poll.
12. Atomic managed-buffer ownership balances under concurrent clone, detach,
    and release stress.
13. Copy-on-write mutation preserves snapshot semantics under cross-worker
    immutable sharing.
14. Handler delimiters and frame-bound capabilities cannot cross a parallel
    task boundary.
15. Baseline WASM local execution and threads-enabled WASM execution produce
    results permitted by the same semantics.
16. Encoded bytecode validation rejects forged wakers, invalid task generations,
    non-atomic cross-worker ownership operations, and concurrent-poll states.
17. Native race-detection and scheduler stress lanes run where toolchains are
    available; their absence is not replaced by timing-only unit tests.
18. Benchmarks report atomic ownership cost, parallel speedup, work, span, wake
    traffic, queue contention, and blocking-pool saturation separately.

## Research and precedent

- Rust `std::future::Future`: `poll` is nonblocking, returns `Pending`, and uses
  the context's waker to request another poll:
  <https://doc.rust-lang.org/std/future/trait.Future.html>.
- Rust `std::task::Waker`: a waker notifies an executor that a task is ready to
  run: <https://doc.rust-lang.org/std/task/struct.Waker.html>.
- Rust Async Book, *Applied: Build an Executor*: lazy futures, ready queues,
  polling, and wake-driven rescheduling:
  <https://rust-lang.github.io/async-book/02_execution/04_executor.html>.
- Rustonomicon, *Send and Sync*: `Send` permits transfer, `Sync` permits shared
  access, `T: Sync` iff `&T: Send`, and non-atomic `Rc` and unsynchronized
  interior mutability are excluded:
  <https://doc.rust-lang.org/nomicon/send-and-sync.html>.
- Rust `Arc`, *Thread Safety*: atomic ownership does not make a non-thread-safe
  payload thread-safe:
  <https://doc.rust-lang.org/std/sync/struct.Arc.html#thread-safety>.
- Jung et al., *RustBelt: Securing the Foundations of the Rust Programming
  Language*, POPL 2018: semantic foundations for unsafe abstraction and
  ownership-based concurrency: <https://plv.mpi-sws.org/rustbelt/popl18/>.
- Weiss, Patterson, and Ahmed, *Oxide: The Essence of Rust*, 2019: a formal
  ownership and borrowing calculus used already by Talk's place-based
  ownership design.
- Blumofe and Leiserson, *Scheduling Multithreaded Computations by Work
  Stealing*, JACM 1999: the fully strict work-stealing bound:
  <https://dl.acm.org/doi/10.1145/324133.324234>.
- Chase and Lev, *Dynamic Circular Work-Stealing Deque*, SPAA 2005: the
  concurrent deque lineage for practical work-stealing executors.
- Batty et al., *Mathematizing C++ Concurrency*, POPL 2011: the memory-model
  foundation inherited by Rust and native target atomics:
  <https://dl.acm.org/doi/10.1145/1926385.1926394>.
- Halstead, *Multilisp: A Language for Concurrent Symbolic Computation*, TOPLAS
  1985: futures as independently scheduled computations whose results become
  available later.

## Relationship to existing decisions

- **ADR 0032:** preserves Copy/Affine/Linear grades, exclusive borrowing,
  deterministic cleanup, and current one-shot handler behavior. `Send` and
  `Sync` are orthogonal to value grade.
- **ADR 0039:** preserves ordinary source handlers and the ban on
  compiler-known host-effect policy. Core future implementations use source
  effects; no effect gains a magical runtime miss path.
- **ADR 0044:** on acceptance, narrows the concurrency boundary by admitting
  thread-safe ownership transitions for representations that satisfy checked
  `Send`/`Sync`. Substrate-specific ownership and no dynamic promotion remain.
- **ADR 0047:** finalized MIR remains the only target seam; executor semantics
  do not create a backend-specific source interpretation.
- **ADR 0049:** effect-handler elimination remains valid because future polling
  does not change effect identity or routing.
