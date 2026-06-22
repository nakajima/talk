# ADR 0003: First-class protocol existentials

## Status

Accepted; implemented.

## Context

Talk protocols currently use static evidence: generic protocol calls are checked with qualified predicates and lowered through concrete witness selection. That remains the default for generic code.

GADTs add another need: a constructor can hide a case-local type parameter. Returning or storing a hidden value requires a first-class existential package rather than exposing the hidden type.

Research basis checked for this ADR:

- Mitchell and Plotkin, *Abstract Types Have Existential Type* (TOPLAS 1988): abstract values are existential packages, `pack representation + operations as exists T. interface`, and the package type must be known to avoid ambiguity.
- Jones, *A Theory of Qualified Types* (ESOP 1992 / revised SCP version): protocol constraints are predicates with evidence; using a constrained value requires suitable evidence for the predicate.
- Wadler and Blott, *How to make ad-hoc polymorphism less ad hoc* (POPL 1989), and Hall, Hammond, Peyton Jones, and Wadler, *Type Classes in Haskell*: class/protocol dictionaries are the standard evidence translation for overloaded operations.
- Chakravarty, Keller, and Peyton Jones, *Associated Type Synonyms* (ICFP 2005): associated types are type functions; useful signatures constrain them with equality evidence such as `Elem c = Int`.
- Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann, *OutsideIn(X)* (JFP 2011): local assumptions, type functions, and ambiguity should be handled with explicit constraints rather than inference guesses.
- Oliveira, Moors, and Odersky, *Type Classes as Objects and Implicits* (OOPSLA 2010): type-class evidence can be represented as objects/implicit parameters, reinforcing the payload-plus-evidence model.

## Decision

Add first-class protocol existential syntax in the form:

```talk
any Showable
any Iterator<Element = Int>
```

The v1 surface is intentionally narrow:

- exactly one protocol after `any`;
- no protocol composition such as `any A & B`;
- associated bindings are named, not positional;
- all associated types from the protocol and its supers must be specified;
- associated bindings are equality bindings only;
- no bound-only associated forms such as `any Collection<Element: Showable>`;
- no explicit source `open` construct in v1.

## Type representation

Use a dedicated type-system representation:

```rust
Ty::Any {
    protocol: Symbol,
    assoc: Vec<(Symbol, Ty)>,
}
```

The `assoc` vector is canonicalized by associated-type symbol. The denotation is:

```text
any P<Assoc = T>
  ~= exists Self. Self * evidence(Self: P) * evidence(Self.Assoc = T)
```

This is a real existential type former. A compiler-synthesized enum is only a possible lowering strategy, not the source-of-truth type.

## Object safety and members

`any P` is valid only when `P` is object-safe for v1:

- every superprotocol used by the existential is object-safe;
- requirements must be callable through a receiver;
- requirement signatures must not mention `Self` except as the implicit receiver;
- requirements must not have method type parameters;
- all associated types used by the protocol shape must be fixed by equality bindings.

Member lookup on `any P<Assoc = T>` opens the package internally, substitutes the associated equalities, and exposes the erased member signature. A requirement that would expose the hidden `Self` is rejected for existential use.

For example:

```talk
let it: any Iterator<Element = Int> = makeIterator()
it.next() // result uses Int, not a hidden Self.Element
```

## Packing

Implicit packing is allowed only in expected-type positions. The expected type supplies the existential package type, matching Mitchell and Plotkin's need for an explicit package type to avoid ambiguity.

Allowed examples:

```talk
let x: any Showable = 123

func make() -> any Showable {
    123
}
```

Packing `source: S` into expected `any P<Assoc = T>` emits ordinary wanted predicates:

```text
S: P
S.Assoc == T
```

If those constraints solve, the checker records a pack site for lowering.

## No existential upcasting in v1

V1 does not support existential-to-existential coercions:

```talk
protocol Readable {
    func read() -> String
}

protocol ReadWrite: Readable {
    func write(value: String)
}

let rw: any ReadWrite = makeReadWrite()
let r: any Readable = rw // rejected in v1
```

This is an implementation boundary, not a soundness impossibility. A later version can add explicit existential upcasts once witness-bundle layout is stable.

## Implicit-pack no-upcasting guard

The implicit-packing path must not use synthesized self-conformance to smuggle an existential upcast.

When the checker has expected type `E = Ty::Any { protocol: P, assoc: A }` and inferred source type `S`:

1. If `S` is the same canonical `Ty::Any { protocol: P, assoc: A }`, accept it as an ordinary assignment with no pack.
2. If `S` is any other `Ty::Any`, reject in v1 as an unsupported existential upcast/repack.
3. Otherwise, try ordinary concrete/generic packing by solving `S: P` plus the associated equality bindings.

This guard has priority over synthesized existential self-conformance. Without it, this program could be accepted by nesting an `any ReadWrite` inside an `any Readable`, even though direct upcasting is supposed to be out of scope:

```talk
let rw: any ReadWrite = makeReadWrite()
let r: any Readable = rw // must not become pack(rw) via any ReadWrite: Readable
```

Nested existential packing may be useful later, but v1 rejects it so the no-upcasting rule is visible and predictable.

## Synthesized self-conformance

For an object-safe existential, synthesize forwarding conformance so `any P` can satisfy generic `T: P` bounds:

```talk
func show<T: Showable>(value: T) -> String {
    value.show()
}

let x: any Showable = 123
show(x) // allowed when Showable is object-safe
```

The synthesized witness forwards through the package's runtime witness table. This self-conformance is for generic constraints and member dispatch; it is not an implicit existential upcast mechanism.

## Runtime model

The runtime representation is a package:

```text
payload + witness table/bundle
```

Associated equality bindings are type-checker evidence. Runtime metadata is needed only if a future feature performs runtime type tests, equality across erased values, or explicit opening with type reflection.

The package is a normal first-class value: it can be stored in structs, records, arrays, options, closures, and returned from functions.

## Deferred

- explicit `open` syntax;
- protocol compositions (`any A & B`);
- bound-only associated constraints;
- existential upcasting;
- structural equality/typecase for existential packages;
- exposing non-object-safe requirements through `any P`.
