# 0051 - Function-value effects resolve at invocation

Status: accepted; implemented

## Context

Talk's handlers have dynamic extent, but anonymous function values previously
captured one concrete handler capability per latent effect when the closure was
created. This made an ordinary higher-order handler impossible:

```talk
effect 'throw<T: Showable>(val: T) -> T
func rescue<T: Showable>(fn: () 'throw -> T) -> T {
    #handle 'throw { value in 'continue value }
    fn()
}

rescue { 'throw(val: 3) }
```

The callback was created before `rescue` installed its handler, so closure
construction executed `FindHandler('throw)` and trapped. Contextual effect
widening made the mismatch sharper: even `rescue {}` was assigned the expected
effectful function type and performed the same lookup despite its pure body.
A valid subeffecting coercion therefore changed runtime behavior.

Standard algebraic-handler semantics treats a function's effect row as a
latent requirement of executing the function. A handler around that execution
handles operations from callees and callbacks in its dynamic extent. Research
on abstraction-safe handlers refines this with tunneling: higher-order code
must not accidentally handle effects it is polymorphic over. Talk's handlers
are explicitly label-scoped, so a handler is aware of exactly the labels it
names; code with no handler for a label cannot intercept it.

## Decision

Function-value effects resolve against the handler stack at invocation:

- A closure environment contains captured values, cells, and inherited generic
  evidence, but no effect-handler capabilities.
- A perform in a closure body emits the same `FindHandler` operation as a
  perform in a named function. The lookup runs when the body executes and
  selects the nearest handler above the current search floor.
- Contextually checked closures check their bodies under a fresh latent effect
  row. The expected function row is an upper bound, not authority that closure
  creation must acquire. Closed bounds use label-scoped effect inclusion, so a
  generic declaration such as bare `'throw` admits checked instantiations such
  as `'throw<Int>`.
- Pure-to-effectful widening remains operationally inert: a pure closure may be
  used at an effectful function type without looking up any handler.
- Handler clauses still execute outside their own search floor. Re-performing
  the same label delegates to the next outer handler exactly as before.

This changes the same-label nested-handler example deliberately. If a closure
is created under handler A and invoked under nearer handler B, its perform now
routes to B. Lexical value capture is unchanged; only effect routing changes.

Talk does not add a second `dynamic` function kind or a capture-if-present
fallback. Those alternatives make equal function types route differently based
on creation history. First-class named handler instances and full
fresh-identity tunneling remain possible extensions; the current explicit
label on `#handle` is the language's awareness boundary.

## Consequences

- Higher-order handlers such as `rescue`, transactions, state runners, and
  scoped resource interpreters can handle effects from supplied computations.
- Function values can be created outside a user handler and safely invoked
  inside one.
- Closure environments are smaller and no longer retain frame-bound handler
  delimiters.
- Moving a function value does not implicitly move handler authority. Its call
  must occur in an extent that supplies every effect it actually performs;
  ambient effects continue to reach Core's outer fallback handlers.
- Existing programs that relied on creation-site routing now select the
  invocation site's nearest handler instead.
- Whole-program handler elimination still scans reachable closure bodies for
  `FindHandler`; the lookup moved from closure construction into execution but
  remains explicit MIR.

## References

- Plotkin and Pretnar, *Handlers of Algebraic Effects*.
- Leijen, *Type Directed Compilation of Row-Typed Algebraic Effects*.
- Zhang and Myers, *Abstraction-Safe Effect Handlers via Tunneling*, POPL 2019.
- Brachthaeuser, Schuster, and Ostermann, *Effekt: Capability-Passing Style for
  Type- and Effect-Safe, Extensible Effect Handlers in Scala*.
