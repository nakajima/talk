# ADR 0016: Protocol arguments in conformance identity

## Status

Proposed.

## Context

Talk currently treats a conformance predicate as `Self: Protocol`. In the
checker this shows up as `Conforms { ty, protocol }`, `Ty::Proj(base,
protocol, assoc)`, and conformance rows keyed by `(head, protocol)`.

That model makes every associated type a function of `Self` and `Protocol`
alone. It is coherent for protocols such as `Iterator`, where one iterator type
has one `Element`, but it cannot express operator-style protocols where one
left-hand type may support many right-hand types:

```talk
String: Add<String>
String: Add<Character>
```

If `RHS` were an associated type on `Add`, then `String.RHS` and `String.Ret`
would be underdetermined. The varying type must be an input to conformance
selection, not an output associated with `Self` alone.

## Decision

Protocol applications are first-class conformance targets. Internally, use a
protocol reference:

```rust
pub struct ProtocolRef {
    pub protocol: Symbol,
    pub args: Vec<Ty>,
}
```

A conformance row's logical identity is the full instance head:

```text
(SelfPattern, ProtocolRefPattern)
```

A fully instantiated conformance key is:

```text
(SelfTy, Protocol, ProtocolArgs)
```

Therefore these are distinct conformances:

```talk
protocol Add<RHS> {
    associated Ret
    func add(rhs: RHS) -> Ret
}

extend String: Add<String> {
    typealias Ret = String
    func add(rhs: String) -> String { ... }
}

extend String: Add<Character> {
    typealias Ret = String
    func add(rhs: Character) -> String { ... }
}
```

Associated types are outputs of the selected full protocol application. The
semantic projection is:

```text
<Self as Add<RHS>>::Ret
```

not:

```text
Self.Ret
```

Source may keep shorthand such as `T.Ret` only when the surrounding predicates
identify exactly one protocol reference that owns `Ret`. Otherwise the program
must use an explicit qualified projection syntax once one exists, or the checker
reports an ambiguity.

## Rules

- Protocol arguments are input parameters to conformance selection.
- Associated types remain output projections from the selected conformance.
- At most one conformance row may apply to a fully instantiated key
  `(SelfTy, Protocol, ProtocolArgs)`.
- Overlapping rows are rejected unless the language later adds an explicit
  specialization relation. V1 should not add specialization.
- A use whose protocol arguments are not determined must defer while inference
  can still determine them, then report ambiguity if multiple rows remain.
- Solver and lowering must never select a row by catalog order.

## Predicate and type representation

Change the predicate and constraint forms from protocol symbols to protocol
references:

```rust
Predicate::Conforms { ty: Ty, protocol: ProtocolRef }
Constraint::Conforms { ty: Ty, protocol: ProtocolRef, origin: CtOrigin }
```

Change associated projections to carry the full protocol reference:

```rust
Ty::Proj(Box<Ty>, ProtocolRef, Symbol)
```

`Ty::Any` should also carry a protocol reference:

```rust
Ty::Any {
    protocol: ProtocolRef,
    assoc: Vec<(Symbol, Ty)>,
}
```

The existential's protocol arguments are part of the existential type. The
`assoc` list still fixes output associated types by equality.

## Catalog representation

A conformance row records both the self-head pattern and the protocol-argument
pattern:

```rust
pub struct Conformance {
    pub params: Vec<Symbol>,
    pub self_args: Vec<Ty>,
    pub protocol_args: Vec<Ty>,
    pub context: Vec<Predicate>,
    pub witnesses: FxHashMap<String, Symbol>,
    pub assoc: FxHashMap<Symbol, Ty>,
}
```

Do not rely on an exact `FxHashMap<(Symbol, Symbol), Conformance>` as the source
of truth: generic rows contain patterns, so exact hashing of the argument vector
is not enough. Instead, store rows with stable row ids and index them for lookup:

```text
(head symbol, protocol symbol) -> [ConformanceId]
```

Coherence checks and solver lookup operate on the full row:

```text
(SelfHead(self_args), Protocol(protocol_args))
```

For concrete monomorphic rows, the logical key is still the full instantiated
triple `(SelfTy, Protocol, ProtocolArgs)`.

## Solver lookup

To solve `T: P<Args...>`:

1. Normalize `T` and every protocol argument through the current store and
   givens.
2. If the self head is still unknown, defer the constraint.
3. For a nominal self type, collect candidates from `(head, P)`.
4. Pattern-match both the row's `self_args` and `protocol_args` against the
   actual self arguments and requested protocol arguments, producing one shared
   substitution for row params.
5. Discard non-matching rows.
6. If exactly one row matches, enqueue its substituted context predicates.
7. If no row matches, report `NotConforming` or try derivation where allowed.
8. If multiple rows match, report ambiguous conformance.

Projection normalization uses the same selected row. To reduce
`Proj(T, P<Args...>, Assoc)`, first resolve `T: P<Args...>`, then substitute the
row's associated binding with the same row substitution.

## Superprotocols and bounds

Protocol supers and bounds must also carry protocol references:

```talk
protocol Comparable<RHS>: Equatable<RHS> {
    func gt(rhs: RHS) -> Bool
}
```

A bound `T: Comparable<Int>` entails `T: Equatable<Int>`, not `T: Equatable` in
isolation. `param_bounds` should become `Vec<ProtocolRef>` rather than
`Vec<Symbol>`.

Associated-type bounds continue to work, but their predicates are over protocol
references. For example:

```talk
protocol Iterable {
    associated Element where Element: Showable
}
```

still records a bound on the associated output `Element`; if that bound itself
uses a protocol with arguments, it is represented as a `ProtocolRef`.

## Member resolution

Requirement lookup is by protocol symbol, but dispatch is by protocol reference.
For a requirement call such as:

```talk
lhs.add(rhs)
```

member checking uses the requirement signature of `Add<RHS>` and the argument
type to construct or refine the wanted predicate:

```text
typeof(lhs): Add<typeof(rhs)>
```

If several protocol references could own the same member use, the call is
ambiguous unless argument and result context determine a single protocol
reference. The explicit protocol-static form must include protocol arguments:

```talk
Add<Character>.add(lhs, rhs)
```

instead of only:

```talk
Add.add(lhs, rhs)
```

## Source syntax boundary

Positional angle arguments on a protocol application are protocol arguments.
Associated-type equalities should be named or written as ordinary same-type
predicates:

```talk
T: Add<Int>
T: Iterator<Element = Int>
where T.Element == Int
```

The old positional associated-type shorthand, such as `T: Iterator<Element>`, is
not compatible with protocol arguments as a general syntax. It should be
removed, deprecated, or accepted only as a compatibility rewrite for protocols
with zero declared protocol parameters.

## Migration

Protocols whose varying type participates in overload selection should move that
type from an associated type to a protocol argument:

- `Add<RHS>` keeps `Ret` associated.
- `Subtract<RHS>` keeps `Ret` associated.
- `Multiply<RHS>` keeps `Ret` associated.
- `Divide<RHS>` keeps `Ret` associated.
- `Equatable<RHS>` uses `RHS` as an input argument.
- `Comparable<RHS>: Equatable<RHS>` uses `RHS` as an input argument.
- `From<Source>` and `Into<Target>` should be reviewed the same way.

Protocols where the type is uniquely determined by `Self` should keep associated
types:

- `Iterator.Element`
- `Iterable.Element`
- `Future.Output`

This keeps associated types as functional outputs while allowing multiple
coherent conformances to the same protocol family.
