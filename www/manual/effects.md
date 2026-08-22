# 6. Effects

Effects let application code describe what it needs without choosing where that service comes from. A function can request configuration, stop a computation, or pause a task in direct style. A surrounding handler decides what the request means, and the type checker records the possible requests in the function's effect row.

## Separating a request from its answer

Suppose a greeting needs the current user's name. The function should not care whether the name comes from a terminal, a test fixture, or an embedding host:

```tlk
effect 'setting(key: String) -> String?

func greeting() -> String {
    match 'setting(key: "user.name") {
        .some(name) -> "Hello, " + name,
        .none -> "Hello, stranger"
    }
}

#handle 'setting { key in
    let answer = if key == "user.name" { .some("Ada") } else { .none }
    'continue answer
}

greeting()
```

Calling an effect is called *performing* it. The perform suspends at the request, the nearest handler runs, and `'continue answer` resumes the suspended code with `answer` as the result of the effect call. A test can install a deterministic handler while production code installs one backed by real configuration. `greeting` stays ordinary direct-style code in both cases.

The handler's extent is the code after the `#handle` statement in the same block, including functions called from there. Code before the statement is unaffected. If handlers are nested, the nearest handler for the same effect label wins.

## Effect rows

Effects are part of function types. A closed function effect can be written in three forms:

```tlk
func pure() '[] -> Int { 42 }
func writes() 'io -> Void { print("hello") }
func both(flag: Bool) '[io, panic] -> Void {
    print("hello")
    if flag { unreachable }
}

pure()
```

`'[]` is explicitly pure, `'io` names one closed effect, and `'[io, panic]` names several. `'[io, ..]` requires `io` while leaving the rest of the row open for inference. A function with no written row receives an open inferred row, so effects normally propagate through callers without annotations.

A function value carries the same invocation requirement:

```tlk
let action: () 'io -> Void = func() { print("hi") }
action()
```

The row says what may happen when the value is invoked. A closure does not freeze the handler active when it was created; performs use the handlers active at the call site. This is what lets a higher-order function install a handler around a callback.

## Stopping a computation

A handler does not have to continue. Completing the clause aborts the handled computation and unwinds its frames. This can remove repetitive error plumbing when a whole operation has one failure boundary:

```tlk
effect 'reject(message: String) -> Never

func checked_port(_ value: Int) -> Int {
    if value < 1 || value > 65535 {
        'reject(message: "port is out of range")
    }
    value
}

func configured_port(_ value: Int) -> Int {
    #handle 'reject { message in
        print("invalid configuration: " + message)
        return 8080
    }
    checked_port(value)
}

configured_port(70000)
```

`checked_port` declares the exceptional operation once. `configured_port` chooses the policy for that boundary. Cleanup still runs while the abandoned frames unwind, so aborting an effect does not skip `Deinit` hooks.

`unreachable` follows this model: it performs the public `'panic` effect and never returns. A program may handle it explicitly; otherwise the outer host reports the panic and terminates.

## Re-performing and delegation

A handler clause runs outside its own search floor. If it performs the same label again, lookup continues with the next outer handler rather than recursively selecting itself. This lets a handler inspect, transform, or log a request and delegate it to the host fallback.

## Capturing resumptions

Most clauses use `'continue` immediately. A clause may instead bind the suspended continuation as an additional final parameter and store it as a value:

```tlk norun
effect 'emit(value: Int) -> ()

enum Step {
    case yielded(Int, Resumption<(), Step>)
    case done
}

func generate() -> Step {
    #handle 'emit { value, continuation in
        Step.yielded(value, continuation)
    }
    'emit(value: 1)
    Step.done
}
```

The extra binder changes the clause from tail-resumptive to resumption-binding. `resume(k: continuation, value: ())` continues the suspended extent later. `cancel(k: continuation)` abandons it and runs cleanup. A `Resumption` is linear and one-shot: every finite path must consume it exactly once, and two workers cannot resume the same continuation.

This mechanism powers generators and TalkTalk's cooperative scheduler. Waiting on a channel or deadline can store the current task's resumption and run another task without rewriting the waiting function as a state machine.

## Generic effects

Effects may be generic:

```tlk norun
effect 'echo<T>(value: T) -> T
```

Effect rows track separate instantiations. One handler for an effect label covers every generic instantiation in its extent, and the handler body is checked generically. Resumption-binding clauses currently have tighter restrictions than immediate `'continue` clauses: in particular, they cannot bind resumptions for type-generic effects or effects with `mut` parameters.

## Built-in host effects

Core uses effects for input and output, memory allocation, task suspension, and panic. They are not compiler-privileged operations: Core installs ordinary outer handlers that connect them to the host. A nearer application handler may intercept the same request.

## Further reading

TalkTalk's design belongs to the algebraic-effects and handlers family:

- [Handlers of algebraic effects](../../papers/plotkin-pretnar-2013-handling-algebraic-effects.pdf) gives the foundational handler model.
- [Type directed compilation of row-typed algebraic effects](../../papers/leijen-2016-row-typed-algebraic-effects.pdf) explains effect rows and their compilation in Koka.
- [Zero-cost effect handlers by staging](../../papers/schuster-brachthaeuser-ostermann-2019-zero-cost-effect-handlers.pdf) explores efficient handler compilation.

The exact choices made by TalkTalk, including generic handlers and invocation-time handler lookup, are recorded in [Effect semantics and implementation](../../docs/effects.md).
