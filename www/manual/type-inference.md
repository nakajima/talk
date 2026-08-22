# A. Type Inference Reference

TalkTalk uses local, constraint-based type inference. The checker assigns a type to every expression, infers polymorphic signatures where it can, selects protocol witnesses, records effect rows, and publishes the concrete substitutions the compiler will specialize. This appendix describes where information comes from, what becomes generic, and when an annotation is required.

## Unknowns and constraints

When the checker encounters an expression whose type is not known, it creates a type variable. It does not immediately guess a concrete type. Instead it records constraints:

- two types, record rows, or effect rows must agree;
- a type must conform to a protocol;
- a receiver must have a named member of a particular type;
- one value must adapt to the type expected at its use;
- a static generic value must satisfy an equality or comparison.

The solver repeatedly uses new information until no constraint can make further progress. Information therefore flows in both directions and across source order:

```tlk
let values = []
values.push(42)

values.count
```

The empty array begins as `[Element]` for an unknown `Element`. `push(42)` later constrains `Element` to `Int`; the final expression returns the array's count.

An inconsistent constraint produces a diagnostic at the operation that introduced it. An unsolved but potentially reusable constraint may instead become part of an inferred generic signature.

## Inference and checking

Expression typing has two modes.

In *inference* mode, the expression produces a type. The literal `42` can produce `Int`, and a function literal produces a function type from its parameters, body, and effects.

In *checking* mode, the context supplies an expected type and the checker pushes it inward. Expected types explain leading-dot enum cases, closure parameters, empty collections, existential packing, and GADT match results:

```tlk
let count: Int? = .some(3)
let transform: (Int) -> Int = func(value: Int) -> Int { value + 1 }

(transform(count!))
```

`.some` is resolved as `Optional<Int>.some` from the annotation. The function type tells the closure that `$0` is an `Int`.

If an expression first infers a type and its context expects another, the adaptation judgment decides whether ordinary equality, borrowing, value sharing, cloning, conversion, or existential packing is permitted. The compiler records that decision once; later phases do not guess again.

## Function bodies

An unannotated function gets unknown parameter and result types. Operations in the body constrain them:

```tlk
func add_one(value) {
    value + 1
}

add_one(41)
```

The integer operation constrains `value` and the result. A final expression constrains the return type. An explicit `return` contributes the same constraint, and all reachable returns must agree.

A written annotation is a requirement, not a hint:

```tlk
func size(_ text: String) -> Int {
    text.count()
}

size("hello")
```

The body is checked against `String` and `Int`. Public declarations may infer types, but annotations make an API easier to understand and keep later implementation edits from silently changing it.

## Binding groups and recursion

Top-level functions and values are ordered by their references. Mutually dependent declarations form a strongly connected binding group and are checked together.

Every declaration in a group first receives a monomorphic skeleton. Recursive calls use that skeleton while the body is being checked, so recursion cannot call itself at unrelated types. After the whole group solves, eligible unknowns may be generalized.

```tlk
func sum_to(n) {
    if n <= 0 { return 0 }
    n + sum_to(n - 1)
}

sum_to(255)
```

The recursive uses consistently constrain `n` and the result to `Int`. This example uses addition so ordinary inputs such as `255` stay within TalkTalk's machine-sized `Int`; an unchecked factorial would overflow quickly.

A non-recursive inferred function can be used at several types when its remaining constraints support that polymorphism. The compiler instantiates its finished signature independently at each use.

## Generalization

A polymorphic signature is conceptually:

```text
forall parameters. predicates => type
```

`func identity(value) { value }` leaves one type unknown but consistently shared between parameter and result, so it generalizes to the equivalent of `<T>(T) -> T`.

Generalization occurs for eligible top-level binding groups. It is restricted to syntactic values such as functions and constants. An evaluated expression that can create or observe mutable state remains monomorphic. If one binder in a recursive group fails this value restriction, the group remains monomorphic.

Local `let` bindings inside function bodies do not generalize. Each local has one type for that invocation. Write a generic function declaration or an explicitly generic closure-bearing API when local polymorphism is required.

Written generics are rigid while their body is checked:

```tlk
func pair<T>(_ value: T) -> (T, T) {
    (value, value)
}

pair(42)
```

The body must work for every `T`; it cannot specialize `T` to the first concrete operation that happens to use it.

## Instantiation and specialization

Using a polymorphic declaration replaces each quantified parameter with a fresh unknown and re-emits its predicates. Solving determines a substitution for that use:

```tlk
func identity(value) { value }

let number = identity(42)
let text = identity("hello")

(number, text)
```

The compiler records `T = Int` at the first call and `T = String` at the second. Lowering creates concrete specialized implementations. Generic types and protocol evidence do not require runtime type tags merely because source inference omitted annotations.

Explicit generic arguments can pin an otherwise inferred substitution when needed.

## Protocol constraints

A generic operation can leave a protocol obligation rather than one concrete type. In this function, `<` requires `Comparable<T>`:

```tlk
func smaller<T: Comparable<T>>(_ a: T, _ b: T) -> T {
    if a < b { a } else { b }
}

smaller(3, 7)
```

Declared bounds and inferred obligations share one predicate system. At each call, the solver chooses a conformance and records the witness used by specialization.

Associated types are projections selected by a conformance. Equality constraints such as `I.Element == Int` may be declared in `where`, or an associated equality may be retained when a function body proves it is part of the inferred API. Ordinary undeclared same-type requirements are not silently added to a written generic signature.

A generic parameter mentioned only in constraints but not determined by parameters, result, `Self`, or a connecting equality is ambiguous and rejected.

## Member inference

`receiver.member` creates a member constraint. If the receiver type is known, lookup resolves a struct field or method, enum member, protocol requirement, conformance witness, or record field.

If the receiver is still unknown, the constraint can ride an inferred signature:

```tlk norun
func run(value) {
    value.go()
}
```

Conceptually, `run` says that its parameter has a `go` member with the inferred callable type. Different call sites may satisfy that requirement with unrelated nominal methods or with a record field containing a function. Each specialization resolves the member statically.

When several protocol requirements provide the same label and none is preferred by the types, lookup is ambiguous. Use protocol-qualified syntax to select the intended requirement.

## Record rows

A record type is a sorted set of labeled field types and an optional tail.

A *closed* row has exactly its listed fields:

```tlk
let point: { x: Int, y: Int } = { y: 2, x: 1 }
```

An *open* row has required fields plus an unknown remainder. Field access on a parameter naturally infers one:

```tlk norun
func name(value) {
    value.name
}

name({ id: 1, name: "Ada" })
name({ active: true, name: "Grace" })
```

The inferred parameter is approximately `{ name: T, ..row }`. Unifying rows matches fields by label, unifies matching field types, and sends fields found on only one side into the other side's tail. A closed row has no tail and therefore cannot absorb an extra or missing field when exact equality is required.

Row parameters are generalized and instantiated like type parameters. The recorded call-site row is intended to become concrete before MIR layout, so every runtime field offset is static. The current executable backends do not yet cover every inferred open-row value, including the generic `name` example above. Closed records and patterns over concrete scrutinee shapes are supported; use `..` to ignore known extra fields.

## Effect rows

Every function type carries the effects that invoking it may perform. A function without a written effect annotation begins with an open row, and performed operations or effectful calls add entries to it:

```tlk
func report(message) {
    print(message)
}

report("done")
```

`report` infers the host effects required by `print`. A higher-order function's row can retain an open tail standing for effects of its callback. This is effect polymorphism: a pure callback does not acquire effects merely because another callback could have them.

A handler removes its handled occurrence from the surrounding row. Function values resolve handlers at invocation, so effect widening does not capture runtime authority.

Written closed rows are upper bounds checked at the declaration:

- `'[]` permits no effects;
- `'io` permits one closed effect;
- `'[io, panic]` permits that set;
- `'[io, ..]` requires `io` and leaves a tail open.

Generic effect labels include their type arguments in the row. Separate instantiations remain distinct even though one label-scoped handler can handle them generically.

## Patterns and GADTs

A pattern constrains its scrutinee and introduces types for bindings. Enum payload types come from the selected constructor. All alternatives in an or-pattern must introduce compatible bindings.

A GADT case can refine the enum's result type inside one match arm. The checker treats those refinements as local givens: they can prove constraints in that arm but cannot unsafely rewrite assumptions outside it.

When all arms infer one common result, the match can infer it. When the only possible result type changes according to distinct GADT refinements, there is no principal type to guess; annotate the function return or the binding receiving the match.

After solving, exhaustiveness checking removes impossible GADT cases and checks the remaining constructor space. It also warns when an earlier arm makes a later arm unreachable.

## Static value inference

A `static` generic parameter is a compile-time value that participates in type identity:

```tlk
func length<static N: Int>(_ values: [Int; N]) -> Int {
    N
}

length([1, 2, 3])
```

The inline array constrains `N` to `3`. Static equalities and comparisons are solved as predicates. The accepted expression language is intentionally limited so static normalization and specialization remain predictable.

## Literals and defaulting

A contextual type can determine a literal through its expected operation or collection element. Without useful context, built-in integer, floating-point, Boolean, character, and string literals use their ordinary core types.

Defaulting happens only after ordinary solving has stopped. It resolves safe conventional leftovers, such as a borrow permission that was never forced exclusive. It does not invent a nominal receiver when several declarations could satisfy a member, choose an arbitrary protocol conformance, or guess a GADT result with no principal type.

## When to annotate

Add an annotation when:

- it is part of a public API contract;
- an empty collection or leading-dot case has no useful context;
- overloaded members or conformances remain ambiguous;
- a recursive group needs a signature stronger than monomorphic recursion can infer;
- a GADT match has no principal result type;
- an existential package must be selected explicitly;
- a closed effect boundary should reject newly introduced effects; or
- the inferred type is correct but obscures intent.

Do not add annotations merely to help downstream code generation. Once type checking succeeds, the compiler's recorded types, substitutions, witnesses, and adaptations are the sole semantic input to lowering.

## Inspecting inferred types

Use editor hover or the command line:

```sh
talk hover source.tlk --line 10 --column 5
```

The REPL's `/type` command is useful for isolated expressions. Rendered inferred signatures may expose generated parameter names or internal member predicates when no source syntax expresses the full qualified type; those names describe the solved scheme rather than a required annotation spelling.

## Further reading

The implementation overview in `talk-front/src/types/README.md` maps this model to compiler modules. The main research lineages are Hindley-Milner generalization, OutsideIn(X) constraints and implications, qualified types and type classes, row-polymorphic records, Koka-style effect rows, and bidirectional GADT checking. Papers cited by that implementation document are mirrored under `papers/`.
