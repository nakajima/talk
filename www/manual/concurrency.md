# 11. Concurrency

TalkTalk has two complementary ways to run work: cooperative tasks on one worker and structured parallel jobs across workers. Both use direct-style source. Code can sleep or wait for a channel while still reading from top to bottom.

Most APIs in this chapter come from `task`. Core supplies the task effects and runs every executable's top-level statements as an implicit cooperative root task. The `coop` module is only needed for an explicit nested scheduling scope.

## Function coloring and direct style

In many languages a function that may pause must be declared `async`, returns a future rather than its ordinary result, and can only be called with `await`. Every caller that wants to pause in turn becomes `async`. The two incompatible call chains are often called *function colors*.

TalkTalk does not add an async function kind. Waiting is an effect performed from an ordinary function. A handler can resume the suspended computation immediately, block the current worker, or store its one-shot resumption while another task runs. Calls and return values keep their ordinary shape:

```tlk
use task::{ sleep }

func reminder() -> String {
    sleep(.milliseconds(100))
    "time is up"
}

reminder()
```

This does not mean waiting is invisible to the type system. `sleep` performs `wait_until`, and that effect is present in the inferred function row. Effect inference propagates the requirement through callers without requiring `async`, `await`, or a future-valued return type. A closed effect annotation still has to admit the operation.

## The implicit root scheduler

Every executable starts with one root task containing its top-level statements. Core's cooperative scheduler runs that task and every task it spawns. The root does not need a `run` wrapper:

```tlk
'spawn(task: func() {
    print("child starts")
    'yield()
    print("child resumes")
})

print("root")
'yield()
```

`'spawn` adds a child task. `'yield` suspends the current task voluntarily so another ready task can run. The scheduler also switches tasks when one waits for a channel or deadline. If the root finishes while children remain, the scheduler continues until all children finish.

Cooperative tasks do not run simultaneously on the same worker. A task changes only at an explicit suspension operation, which makes direct-style local state straightforward. Scheduling order beyond the documented rules is not an API guarantee.

`coop::run` installs the same scheduler around a closure when a nested scheduling scope is useful. A nearer user-defined handler may intercept the task effects to implement a different local policy.

## Waiting and blocking fallbacks

`sleep` computes an absolute monotonic deadline and waits until that deadline has passed. Spurious or coarse host wakes are harmless because it checks the clock again. Hosts may wake late, never early.

The same wait effects have blocking outer handlers. Code running without a cooperative task handler can block its worker and then continue. The compiler may select this cheaper path when the reachable program does not need cooperative scheduling. `run_blocking` installs the standard blocking host handlers for a runtime worker boundary.

The source operation is the same either way; the nearest handler determines whether the task or the whole worker waits.

## Structured parallel work

`parallel_run` starts one worker per input, waits for every worker, and returns results in input order:

```tlk
use task::{ parallel_run, sleep }

let doubled = parallel_run(
    jobs: [1, 2, 3, 4],
    worker: func(consume value: Int) -> Int {
        sleep(.milliseconds(20))
        value * 2
    }
)

print(doubled)
```

The worker receives each job by ownership and may use the standard host effects for I/O, allocation, yielding, panic, channels, and timers. User-defined handlers from the spawning task do not cross the worker boundary; install those inside the worker when needed.

Jobs and results must conform to `Send`. Native targets transfer them into shared-memory workers using thread-safe ownership transitions. The reference VM gives each worker an isolated machine and structurally copies transferable values. `Send` excludes observable identity, so these implementations have the same source-visible value behavior.

Worker handles never escape. Returning from `parallel_run` proves that every worker has completed and every result has transferred back. Nested parallel scopes use help-based joining so a worker waiting for children can run queued work instead of consuming a pool slot indefinitely. Targets without thread support may run the same structured operation sequentially.

Use cooperative tasks for many waiting operations and local orchestration. Use `parallel_run` for independent jobs that should consume CPU in parallel.

## Channels

Channels transfer values between tasks or workers. They are multi-producer and single-consumer:

```tlk
use task::{ channel }

let (sender, receiver) = channel<Int>()
sender.send(value: 42)
print(receiver.recv())
```

`Sender.clone()` creates another logical producer. `Receiver.recv()` returns the next `T`, or `.none` after every sender has been destroyed and the queue is empty. Destroying the receiver closes the other direction; later sends drop their undelivered values safely.

Channel payloads must be `Send`. A send moves the payload into the runtime queue. A waiting receive suspends its task under the cooperative scheduler or blocks under the host fallback. Sending, receiving, and closing wake waiters through the same check-register-park protocol so a wake racing with a wait is not lost.

## Bounded channels and backpressure

An unbounded sender can produce values faster than the receiver consumes them, causing the queue and memory use to grow without limit. A bounded channel caps queued and reserved values. When it is full, `send` waits until the consumer makes room:

```tlk
use task::{ channel_bounded }

let (sender, receiver) = channel_bounded<Int>(capacity: 8)
let delivered = sender.send(value: 42)

(delivered, receiver.recv())
```

Bounded channels are useful for pipelines, network ingestion, and any producer whose rate should follow a slower consumer. The bound is enforced with an atomic reservation so racing producers cannot overfill it. `send` returns `false` if the receiver closes before delivery; otherwise it returns `true` after enqueueing the value.

Backpressure can expose a real dependency cycle: if every task waits to send to a full queue and no task can receive, the program waits. Capacity is part of the pipeline design, not a substitute for arranging progress.

## Selecting receivers

`select_recv` waits for either of two receivers, chooses the first ready side, and leaves the losing value queued:

```tlk
use task::{ Either, channel, select_recv }

let (left_sender, left) = channel<Int>()
let (right_sender, right) = channel<String>()
left_sender.send(value: 7)

match select_recv(a: left, b: right) {
    .left(value) -> print(value),
    .right(value) -> print(value)
}
```

If both sides are ready, the left side wins. This tie rule is deterministic, not fair; swap the receivers when a caller wants to rotate priority. A closed channel counts as ready and produces `.none`. Wakes are readiness hints rather than claims, so the losing side does not lose its queued value.

## Resumptions are the mechanism

A cooperative wait is an ordinary effect handler with an extra continuation binder. The handler stores the suspended task as a linear `Resumption`, runs other ready tasks, and later resumes it when its channel or deadline becomes ready. Cancellation consumes the same one-shot value and runs cleanup for every suspended frame.

This is why direct-style concurrency does not require compiler-generated future state machines. The source scheduler in Core uses the same effect and resumption features available to application code; runtimes provide only threads, transfer queues, monotonic time, and parking.

## Current boundaries

The task surface is deliberately structured. There are no detached task handles, and dropping a handle cannot silently choose between cancellation and detachment because no such handle escapes. Parallel output order follows input order, but concurrent I/O writes may interleave. Use values or channels to establish an order before printing when deterministic output matters.
