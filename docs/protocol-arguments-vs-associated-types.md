# Protocol arguments vs associated types in TalkTalk

This note explains the distinction between protocol arguments and associated
types in the TalkTalk type system.

The short version:

```talk
protocol Foo<T> {
    func bar() -> T
}
```

means `T` is an input to conformance selection.

```talk
protocol Foo {
    associated T

    func bar() -> T
}
```

means `T` is an output/type member of the selected conformance.

In slogan form:

```text
protocol arguments = inputs to conformance selection
associated types   = outputs of selected conformance
```

This distinction is why TalkTalk needs both.

## Practical explanation

### Protocol arguments

A protocol argument participates in the question being asked of the type system.

```talk
protocol Foo<T> {
    func bar() -> T
}
```

This asks whether a type conforms to a particular application of `Foo`:

```text
Self: Foo<T>
```

So `Foo` is relational. For one `Self`, several `T`s may be valid:

```talk
struct Box {}

extend Box: Foo<Int> {
    func bar() -> Int { 1 }
}

extend Box: Foo<String> {
    func bar() -> String { "one" }
}
```

These are distinct conformances because the full conformance identity includes
the protocol argument:

```text
(Box, Foo, Int)
(Box, Foo, String)
```

This is useful when the extra type is genuinely part of overload or conformance
selection. Examples include:

```talk
protocol Equatable<RHS> {
    func equals(rhs: RHS) -> Bool
}

protocol Add<RHS> {
    associated Ret
    func add(rhs: RHS) -> Ret
}

protocol From<Source> {
    static func from(source: Source) -> Self
}
```

For `Add`, the right-hand side is an input:

```talk
String: Add<String>
String: Add<Character>
```

Those are different capabilities. A `String` may know how to add another
`String`, and may separately know how to add a `Character`.

But this also means a use can be ambiguous if context does not determine the
protocol argument:

```talk
let x = Box().bar()
```

If both `Box: Foo<Int>` and `Box: Foo<String>` exist, the call needs contextual
information to know which protocol application is intended.

### Associated types

An associated type is not an input to choosing the conformance. It is a type
member exposed by the chosen conformance.

```talk
protocol Foo {
    associated T

    func bar() -> T
}
```

For a concrete conformance:

```talk
struct Box {}

extend Box: Foo {
    typealias T = Int

    func bar() -> Int { 1 }
}
```

`T` is projected from the selected conformance:

```text
<Box as Foo>.T == Int
```

So `Box` has one `Foo.T`. A second conformance with a different `T` would be a
duplicate conformance, not a distinct one:

```talk
extend Box: Foo {
    typealias T = String

    func bar() -> String { "one" }
}
```

That would collide with the existing `Box: Foo` conformance.

Associated types are useful when the conforming type determines a natural output
or member type.

The canonical example is `Iterator`:

```talk
protocol Iterator {
    associated Element

    mut func next() -> Element?
}
```

A particular iterator has an element type:

```talk
struct StringIterator {}

extend StringIterator: Iterator {
    typealias Element = Character

    mut func next() -> Character? { ... }
}
```

Generic code can then say:

```talk
func first<I: Iterator>(iter: I) -> I.Element? {
    iter.next()
}
```

The function does not need to name a separate `Element` parameter. The element
type is recoverable from `I` through the selected `Iterator` conformance.

Other associated-type-shaped examples include:

```talk
Iterator.Element
Iterable.Element
Future.Output
Collection.Index
Parser.Result
```

These are not usually inputs to selecting a conformance. They are outputs or
members of the abstraction once the conformance is known.

## Why not drop associated types?

If TalkTalk only had protocol arguments, then `Iterator` would have to be
written like this:

```talk
protocol Iterator<Element> {
    mut func next() -> Element?
}
```

That can express the operation, but it changes the abstraction. Generic users
must now carry the element type explicitly:

```talk
func first<I, Element>(iter: I) -> Element?
where I: Iterator<Element> {
    iter.next()
}
```

Compare that with the associated-type version:

```talk
func first<I: Iterator>(iter: I) -> I.Element? {
    iter.next()
}
```

The associated-type version says directly that the iterator type determines its
element type.

The same applies to collection-like APIs:

```talk
func collect<I: Iterator>(iter: I) -> Array<I.Element>
```

Without associated types, every API has to thread `Element` separately:

```talk
func collect<I, Element>(iter: I) -> Array<Element>
where I: Iterator<Element>
```

That is not just syntactic noise. It loses an important dependency: that
`Element` is determined by `I`.

Associated types are how TalkTalk expresses that dependency.

## Why not make associated types part of the conformance key?

Making associated types part of the key turns them into protocol arguments in
all but syntax.

Suppose we have:

```talk
protocol Iterator {
    associated Element

    mut func next() -> Element?
}
```

If `Element` were part of the conformance key, then these would be distinct
conformances:

```talk
extend MyIterator: Iterator {
    typealias Element = Int
    mut func next() -> Int? { ... }
}

extend MyIterator: Iterator {
    typealias Element = String
    mut func next() -> String? { ... }
}
```

That means `MyIterator` no longer has one element type. Instead, `Iterator` has
become a relation:

```text
Iterator(MyIterator, Int)
Iterator(MyIterator, String)
```

That is exactly the protocol-argument model:

```talk
protocol Iterator<Element> {
    mut func next() -> Element?
}
```

So making associated types part of the key erases the distinction between inputs
and outputs. It says associated types are hidden inputs to conformance selection,
rather than outputs of selected evidence.

This also makes formerly simple generic code underdetermined:

```talk
func use<I: Iterator>(iter: I) {
    let x = iter.next()
}
```

With true associated types, `x` has type `I.Element?`.

If `Element` is part of the key, then `I: Iterator` is incomplete. The program
must also say which `Element` application is intended:

```talk
func use<I, Element>(iter: I)
where I: Iterator<Element> {
    let x = iter.next()
}
```

At that point, `Element` is not an associated type. It is a protocol argument.

## Mixed example: Add

`Add` shows why both mechanisms are useful in one protocol:

```talk
protocol Add<RHS> {
    associated Ret

    func add(rhs: RHS) -> Ret
}
```

Here `RHS` is an input. It participates in selecting the conformance:

```talk
String: Add<String>
String: Add<Character>
```

But `Ret` is an output. Once the full protocol application has been selected,
the result type is known from that conformance:

```text
<String as Add<Character>>.Ret
```

The shape is:

```text
inputs:  Self, RHS
output:  Ret
```

Encoding `RHS` as an associated type would wrongly imply that a `String` has one
right-hand side for `Add`. Encoding `Ret` as a protocol argument would make every
use carry an extra selection input, even though result type is naturally an
output of the selected operation.

## Theoretical explanation

The distinction is the difference between a relation and a function/projection.

### Protocol arguments are relational

```talk
protocol Foo<T>
```

corresponds to a predicate with multiple indices:

```text
Foo(Self, T)
```

There may be many valid facts for the same `Self`:

```text
Foo(Box, Int)
Foo(Box, String)
Foo(Box, Bool)
```

Knowing `Self = Box` does not determine `T`.

This is the multi-parameter class or qualified-predicate view: a protocol
application is a predicate constraining type instantiation.

### Associated types are functional

```talk
protocol Foo {
    associated T
}
```

corresponds to a unary predicate plus a type-level projection:

```text
Foo(Self)
T = <Self as Foo>.T
```

The associated type is selected through the conformance evidence. For a fixed
selected conformance, the projection has one result.

This behaves like a functional dependency:

```text
Self, Foo -> T
```

The point is not that TalkTalk must implement Haskell-style functional
dependencies directly. The point is semantic: associated types express that
some type information is determined by the selected conformance, rather than
being another input to selecting that conformance.

## Research lineage

This design is grounded in several lines of type-system research:

- Wadler and Blott, "How to make ad-hoc polymorphism less ad hoc" (POPL 1989):
  type classes as statically resolved predicates/evidence.
- Mark P. Jones, "A Theory of Qualified Types" (ESOP 1992; later SCP):
  qualified types of the form `P => type`, with predicates constraining
  polymorphic instantiation.
- Mark P. Jones, "Type Classes with Functional Dependencies" (ESOP 2000):
  expressing that some class parameters determine others.
- Chakravarty, Keller, and Peyton Jones, "Associated Type Synonyms" (ICFP
  2005): associated types as type-level functions/projections tied to class
  evidence.
- Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann, "OutsideIn(X)" (JFP
  2011): constraint solving with wanted/given predicates, equality constraints,
  and type-family-like projections.

TalkTalk's split is therefore:

```text
Self: P<A, B>       relational predicate, selected by inputs
<Self as P<A>>.Out  projection from the selected evidence
```

## Design guidance for TalkTalk

Use protocol arguments when the type is part of capability selection:

```talk
Equatable<RHS>
Add<RHS>
Comparable<RHS>
From<Source>
```

Use associated types when the type is determined by the conforming type and the
selected protocol evidence:

```talk
Iterator.Element
Iterable.Element
Future.Output
Collection.Index
Parser.Result
```

When in doubt, ask this question:

```text
Can one Self soundly have multiple conformances that differ only in this type?
```

If yes, it is probably a protocol argument.

```text
String: Add<String>
String: Add<Character>
```

If no, and the type is naturally determined after selecting the conformance, it
is probably an associated type.

```text
StringIterator.Element == Character
```
