# 5. Generics and Protocols

Generics let one function or data type work with many kinds of value. Protocols say what those values must be able to do. Together, they let you reuse code without giving up type checking.

## Generic functions and types

Type parameters use angle brackets:

```tlk accumulate(generics)
func identity<T>(_ value: T) -> T {
    value
}

struct Box<Value> {
    let value: Value
}

identity(42)
```

A bound may appear inline or in a `where` clause:

```tlk
func smaller<T: Comparable<T>>(_ a: T, _ b: T) -> T {
    if a < b { a } else { b }
}

func same<T>(_ a: T, _ b: T) -> Bool
    where T: Equatable<T> & Copy
{
    a == b
}

(
    smaller(3, 7),
    same(4, 4)
)
```

Use `&&` between separate predicates and `&` to compose protocols in one conformance bound.

## Protocols

A protocol may require methods, initializers, static methods, and associated types. It may also provide default implementations:

```tlk norun accumulate(protocols)
protocol Named {
    func name() -> String
}

protocol Pet {
    associated Food: Named
    func favorite_food() -> Food

    func description() -> String {
        "a pet who likes " + self.favorite_food().name()
    }
}
```

`Self` names the conforming type.

## Extensions and conformances

An extension adds methods or declares conformance:

```tlk accumulate(protocols)
struct Kibble {}

extend Kibble: Named {
    func name() -> String { "kibble" }
}

struct Cat {}

extend Cat: Pet {
    typealias Food = Kibble
    func favorite_food() -> Kibble { Kibble() }
}

print(Cat().description())
```

Generic extensions bind their parameters explicitly:

```tlk accumulate(generics)
extend<T> Box<T> {
    func get() -> T { self.value }
}

Box(value: 42).get()
```

A protocol can also be extended, adding a method to every conformer that meets the extension's constraints.

## Protocol arguments and associated types

Protocol arguments distinguish different conformances, as in `Equatable<RHS>` or `Add<RHS>`. Associated types describe a type selected by a conformance, as `Iterator.Element` does. Associated equality constraints use `==` in a `where` clause.

Protocols and generic parameters may define defaults, for example:

```tlk norun
protocol EqualTo<RHS = Self> {
    func equals(_ other: RHS) -> Bool
}
```

## Existentials

`any P` stores a value behind an object-safe protocol interface:

```tlk
let item: any Showable = 42 as any Showable
print(item)
```

Associated bindings can be written in the existential type:

```tlk norun
typealias IntIterator = any Iterator<Element = Int>
```

A protocol is object-safe when its requirements keep `Self` in receiver position in the ways supported by the compiler. Use a generic parameter when the concrete type should remain known; use `any P` when different conforming types must share one runtime representation.

## Static value generics

A `static` generic parameter is a compile-time value and participates in type identity:

```tlk
func length<static N: Int>(_ values: [Int; N]) -> Int {
    N
}

let pair: [Int; 2] = [10, 20]
print(length(pair))
```

Static constraints use `==`, `<`, and `<=`. Type arguments accept a limited set of compile-time expressions, so types such as `Matrix<N + 1, (M) * 2>` are possible while type checking remains predictable.

## Further reading

TalkTalk's protocols draw from type classes and qualified types:

- [How to make ad-hoc polymorphism less ad hoc](../../papers/wadler-blott-1989-ad-hoc-polymorphism.pdf) introduces type classes.
- [A theory of qualified types](../../papers/jones-1992-theory-of-qualified-types.pdf) develops the constraint system behind them.
- [Type classes as objects and implicits](../../papers/oliveira-moors-odersky-2010-type-classes-as-objects-and-implicits.pdf) compares closely related implementation strategies.

TalkTalk uses both protocol arguments and associated types. [Protocol arguments versus associated types](../../docs/protocol-arguments-vs-associated-types.md) explains why they are separate features in this language.
