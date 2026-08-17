# 0069 - Implicit cooperative root task

Status: accepted, implemented

## Context

ADR 0067 made asynchronous waiting direct-style and provided
`coop::run(main)` for cooperative tasks. Ordinary top-level waiting already
worked through blocking host fallbacks, but using `'spawn` or `'yield`
required wrapping the executable's statements in an explicit closure passed
to `run`.

The executable entry builder already turns the script into a unit-returning
closure so `_with_host` can install the root handlers and preserve a non-unit
program result through its hidden result slot. Requiring a second user-written
entry closure duplicates that boundary.

## Decision

Every executable runs its generated entry closure as the root task of a
cooperative scheduler.

The scheduler and the `'yield` and `'spawn` effects belong to core's entry
surface. `_with_host` accepts the complete `Task` row, installs the host
fallbacks, and then calls `_run_cooperative` with the generated entry closure.
The type checker continues to derive the ambient top-level effect row from
`_with_host`'s callback type, so it admits the task effects without naming
them in the compiler.

The scheduler runs the root task and every task it spawns to completion. When
all tasks are waiting, it registers their channel or timer interests and
blocks through the existing runtime park operation. Host I/O and panic
handlers remain outside the scheduler. Program result storage and global
teardown remain owned by the existing generated entry wrapper.

`coop::run` remains as a thin adapter to the same core scheduler for an
explicit nested scheduling scope. It no longer defines distinct task effects.

Core also publishes a narrower blocking host wrapper. After reachable MIR is
closed, the backend derives the task-only trigger set from the difference
between the two wrappers' callback rows. If reachable code performs none of
those effects, calls to the full task host are replaced with the blocking
wrapper before optimization. The scheduler then becomes unreachable and
blocking-only channel and timer programs retain direct park handling, with no
resumable C frames. The compiler still names no individual effect.

Programs without core retain their existing direct entry behavior.

## Consequences

Top-level task code no longer needs an explicit `run` wrapper:

```talk
'spawn(task: func() {
    print("child")
})

'yield()
print("main")
```

The source semantics are unconditional: top-level code is eligible to act as
the root task without a user-written wrapper. A program that performs no task
operation may use the observationally equivalent blocking entry
specialization.

A completed root task does not end the process while spawned tasks remain;
the scheduler drains them before the existing teardown wrapper runs.

VM and C execution use the same source-level scheduler and retain parity.
