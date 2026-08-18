# 6. Effects

Effects let a function ask the surrounding program to do something, such as provide input, stop early, or pause. A handler decides how to answer that request. TalkTalk keeps track of these requests so callers know what a function may ask for.

## Declaring and performing an effect

Effect names begin with a tick:

```tlk norun
effect 'ask(question: String) -> String

func greeting() -> String {
    let name = 'ask(question: "What is your name?")
    "Hello, " + name
}
```

Calling an effect is called performing it. A function with no written effect row infers one.

## Effect rows

A closed function effect can be written in three forms:

```tlk
func pure() '[] -> Int { 42 }
func writes() 'io -> Void { print("hello") }
func both(flag: Bool) '[io, panic] -> Void {
    print("hello")
    if flag { unreachable }
}

pure()
```

`'[]` is explicitly pure, `'io` names one closed effect, and `'[io, panic]` names several. `'[io, ..]` requires `io` while leaving the rest of the row open for inference.

Effects are part of function values:

```tlk
let action: () 'io -> Void = func() { print("hi") }
action()
```

The row is a requirement of invoking the value. A closure does not freeze the handler that happened to be active when it was created.

## Handling and continuing

`#handle` installs a handler for the subsequent part of the current block and for calls made from there:

```tlk
effect 'ask(value: Int) -> Int

#handle 'ask { value in
    'continue value * 2
}

print('ask(value: 21))
```

`'continue expression` resumes the suspended computation, making the expression the result of the effect call. The nearest handler for the same label wins.

A handler that finishes without continuing aborts the handled computation. That makes effects suitable for exceptions as well as resumable operations:

```tlk
effect 'stop(message: String) -> Never

func guarded(_ body: () -> Void) -> Void {
    #handle 'stop { message in
        print("stopped: " + message)
        return
    }
    body()
}

guarded {
    'stop(message: "done")
}
```

The handler's extent is the code after the `#handle` statement in the same block, not code before it.

## Capturing resumptions

A handler may bind the continuation as an additional final parameter. The resumption is a linear, one-shot value:

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

Call `resume(k: continuation, value: ())` to continue or `cancel(k: continuation)` to abandon it. Either operation consumes the resumption, and cancellation deterministically runs cleanup for suspended frames.

## Generic effects

Effects may be generic:

```tlk norun
effect 'echo<T>(value: T) -> T
```

Effect rows track separate instantiations. One handler for an effect label covers every generic instantiation in its extent, and the handler body is checked generically.

## Built-in host effects

Core uses effects for input and output, memory allocation, task suspension, and panic. `unreachable` performs the public `'panic` effect and never returns. A program may handle it explicitly; otherwise the outer host reports the panic and terminates.

## Further reading

TalkTalk's design belongs to the algebraic-effects and handlers family:

- [Handlers of algebraic effects](../../papers/plotkin-pretnar-2013-handling-algebraic-effects.pdf) gives the foundational handler model.
- [Type directed compilation of row-typed algebraic effects](../../papers/leijen-2016-row-typed-algebraic-effects.pdf) explains effect rows and their compilation in Koka.
- [Zero-cost effect handlers by staging](../../papers/schuster-brachthaeuser-ostermann-2019-zero-cost-effect-handlers.pdf) explores efficient handler compilation.

The exact choices made by TalkTalk, including generic handlers and invocation-time handler lookup, are recorded in [Effect semantics and implementation](../../docs/effects.md).
