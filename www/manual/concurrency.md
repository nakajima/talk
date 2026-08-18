# 11. Concurrency

TalkTalk can run several jobs without making you mark every calling function as `async`. Code can sleep, wait for a message, or run work in parallel while still reading from top to bottom.

Most APIs in this chapter come from the `task` module. Every executable runs its top-level statements as the root task of Core's cooperative scheduler, so ordinary task code does not need to import `coop` or call a scheduler explicitly. The `coop` module remains available when an explicit nested scheduler scope is useful.

## Sleeping without function coloring

```tlk
use task::{ sleep }

print("before")
sleep(.milliseconds(100))
print("after")
```

`sleep` performs the internal wait effect until a monotonic deadline. The same source can run under the blocking host fallback or a cooperative scheduler.

## Structured parallel work

`parallel_run` starts one worker per input, waits for every worker, and returns results in input order:

```tlk
use task::{ parallel_run }

let doubled = parallel_run(
    jobs: [1, 2, 3],
    worker: func(consume value: Int) -> Int { value * 2 }
)

print(doubled)
```

Jobs and results must conform to `Send`. Each worker runs under its own standard handlers for I/O, allocation, yielding, panic, channels, and timers, so operations such as `sleep` can be used directly. User-defined effects must still be handled inside the worker; handlers from the spawning task do not cross the isolation boundary. Worker handles do not escape, so returning from `parallel_run` means the whole group has finished.

## Channels

Channels are multi-producer, single-consumer transfer queues:

```tlk
use task::{ channel }

let (sender, receiver) = channel<Int>()
sender.send(value: 42)
print(receiver.recv())
```

`Sender.clone()` creates another logical sender. `Receiver.recv()` returns the next `T`, or `.none` after every sender has gone away and the queue is empty. Endpoint destruction updates channel lifecycle state automatically.

A bounded channel adds backpressure:

```tlk
use task::{ channel_bounded }

let (sender, receiver) = channel_bounded<Int>(capacity: 8)
let delivered = sender.send(value: 42)

delivered
```

Bounded `send` waits for capacity and returns `false` if the receiver has closed before delivery.

## Selecting receivers

`select_recv` races two receivers, chooses the first ready side, and leaves the losing value queued:

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

If both sides are ready, the left side wins. A closed channel counts as ready and returns `.none`.

## Cooperative tasks and the implicit root scheduler

Core exposes the `'spawn` task effect. Every executable runs inside an implicit cooperative root scheduler that handles spawned tasks, yields, channel waits, and deadlines while code remains in direct style:

```tlk
'spawn(task: func() -> () {
    print("child")
    'yield()
    print("child resumed")
})

print("root")
```

No `coop` import or `run` wrapper is required. The scheduler drains spawned tasks even if the root task finishes first. `coop::run` installs the same scheduler for an explicit nested scope; a nearer user-defined handler may instead intercept the task effects to provide different scheduling behavior within its own scope.

A spawned closure should receive owned state as an argument at worker boundaries rather than capture non-transferable values.

## Resumptions are the foundation

Effects provide the suspension mechanism. A scheduler may continue a resumption later; cancellation consumes it and runs cleanup. Linear resumptions prevent two workers from resuming the same continuation twice.
