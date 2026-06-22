# ADR 0002: GADT prerequisites, OutsideIn refinement, and existentials

## Status

Accepted; implemented.

## Context

ADR 0001 established a unified predicate language for declaration-level `where` clauses and GADT refinements. While planning GADT support, we identified that a narrow Haskell-style implementation would force too many annotation-heavy compromises for TalkTalk's inference-oriented design.

The central research constraints are real:

- Peyton Jones, Washburn, and Weirich, *Wobbly types: type inference for generalised algebraic data types* (2004), identifies the inference-order problem for GADTs, motivates bidirectional checking, and separates match-unification from ordinary inference-unification. This ADR uses that paper as background, but does not adopt wobbly types as an implementation objective.
- Peyton Jones, Vytiniotis, Weirich, and Washburn, *Simple Unification-based Type Inference for GADTs* (ICFP 2006), treats data constructors as ordinary polymorphic functions during construction, but says pattern matching is where constructor result types refine the branch. The same paper distinguishes existentially bound constructor variables and requires a predictable rule for when refinements apply.
- Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann, *OutsideIn(X)* (JFP 2011), gives the implication-constraint shape we already use: local givens check local wanteds without mutating global assumptions, with touchable variables controlling which inference variables may be solved inside a local implication.
- Maranget, *Warnings for pattern matching* (JFP 2007), frames exhaustiveness/reachability as usefulness over constructors. For GADTs, the constructor set must be filtered by result-type satisfiability before applying the usefulness algorithm.

## Decision

Do not implement a compromised GADT v1 that rejects common TalkTalk programs merely because the checker lacks local refinement and existential-package machinery. Instead, record the GADT design decisions and implement the prerequisites first.

## Locked GADT surface decisions

### Case result syntax

GADT cases use explicit per-case result types:

```talk
enum Expr<T> {
    case int(Int) -> Expr<Int>
    case bool(Bool) -> Expr<Bool>
}
```

The result head must be the enclosing enum for v1. This is accepted:

```talk
case int(Int) -> Expr<Int>
```

This is rejected:

```talk
case bad(Int) -> Other<Int>
```

Payload-less cases may also refine the result:

```talk
enum TypeRep<T> {
    case int -> TypeRep<Int>
    case bool -> TypeRep<Bool>
}
```

If a case omits `->`, the result defaults to the enclosing enum applied to its enum parameters:

```talk
enum Option<T> {
    case some(T) // defaults to -> Option<T>
    case none    // defaults to -> Option<T>
}
```

An explicit result equal to the default is allowed but warns in v1:

```talk
enum Color {
    case red -> Color // redundant-result warning
}
```

### Case-local generics

Cases support local generic parameters with inline bounds:

```talk
enum Expr<T> {
    case pair<A, B>(Expr<A>, Expr<B>) -> Expr<(A, B)>
    case showy<A: Showable>(A) -> Expr<A>
}
```

Per-case `where` clauses are not part of the initial syntax. Inline bounds are enough for constructor predicates in the first implementation.

Case-local generics may not shadow enum-level generics:

```talk
enum Expr<T> {
    case bad<T>(T) -> Expr<T> // rejected
}
```

The type checker reports:

```rust
TypeError::GenericShadowing { name }
```

### Constructor use

Data constructors are ordinary polymorphic functions at construction sites. A case-local bound is enforced when constructing the case:

```talk
enum Boxed<T> {
    case showy<A: Showable>(A) -> Boxed<A>
}

Boxed.showy(123) // requires Int: Showable
```

### Pattern refinements

Pattern matching a GADT case introduces arm-local givens from matching the scrutinee type against the constructor result type.

```talk
enum Expr<T> {
    case int(Int) -> Expr<Int>
}

func eval<T>(e: Expr<T>) -> T {
    match e {
        .int(i) -> i // checked with given T == Int
    }
}
```

Implementation shape:

```rust
Constraint::Implic {
    givens: variant_givens,
    wanteds: arm_wanteds,
}
```

The arm result equality is part of `arm_wanteds`, so it is checked under the same refinements as the arm body.

This behavior applies to every pattern site, not just `match`, because TalkTalk desugars `if let` and `let ... else` through the same pattern machinery.

### Or-patterns

V1 rejects or-pattern alternatives with different canonical GADT refinements:

```talk
match e {
    .int(x) | .bool(x) -> x // rejected if .int gives T == Int and .bool gives T == Bool
}
```

Users should split the arms. Supporting this directly would require disjunctive refinement contexts or per-alternative body checking.

### Existentials

Case-local variables that are not determined by the constructor result are existential in patterns.

```talk
enum KeyValue<K> {
    case pair<V>(K, V) -> KeyValue<K>
}
```

Inside `.pair(k, v)`, `V` is hidden. Returning or storing `v` outside the arm leaks that existential unless the value is packed into an expected first-class protocol existential whose predicates can be satisfied. Plain escapes remain rejected with:

```rust
TypeError::EscapingExistential { param }
```

Message:

```text
Existential type {param} escapes this pattern arm; return or store it by packing into an expected protocol existential, or keep it inside the arm
```

This does not prevent using the existential internally through bounds:

```talk
protocol Showable { func show() -> String }

enum KeyValue<K> {
    case pair<V: Showable>(K, V) -> KeyValue<K>
}

func showValue<K>(kv: KeyValue<K>) -> String {
    match kv {
        .pair(_, v) -> v.show()
    }
}
```

### Exhaustiveness and reachability

Coverage must filter impossible variants by checking whether each constructor result is satisfiable against the scrutinee type before running Maranget usefulness.

For:

```talk
enum Expr<T> {
    case int(Int) -> Expr<Int>
    case bool(Bool) -> Expr<Bool>
}
```

coverage of `Expr<Int>` sees `.int` as possible and `.bool` as impossible. Therefore:

```talk
func f(e: Expr<Int>) -> Int {
    match e {
        .int(i) -> i
    }
}
```

is exhaustive, and a `.bool` arm is unreachable.

## Model cleanup decisions

Rename the enum/variant catalog vocabulary while adding GADT support:

- `EnumInfo` becomes `Enum`.
- `VariantInfo` becomes `Variant`.
- Do not add a parallel persistent `VariantSignature` wrapper.
- `Variant` stores the constructor type as a scheme:

```rust
pub struct Variant {
    pub symbol: Symbol,
    pub constructor_scheme: Scheme,
}
```

The constructor scheme has the shape:

```text
forall mentioned_constructor_params. predicates => (payloads...) -> ThisEnum<result_args...>
```

Use-site instantiation is represented by:

```rust
pub struct VariantInstantiation {
    pub argument_types: Vec<Ty>,
    pub result_type: Ty,
    pub givens: Vec<Predicate>,
    pub instantiations: Vec<(Symbol, Ty)>,
}
```

Put `VariantInstantiation` and variant-instantiation behavior in `src/types/variant.rs`.

## Implementation status

The first implementation slice uses this ADR's OutsideIn design directly:

- expected result types are propagated into blocks, if-expressions, and match arms when available;
- inferred match results use the same implication path with a fresh outer result variable;
- each refining match arm is checked under an implication whose givens come from decomposing the constructor result against the scrutinee type;
- implication solving uses touchability so local refinements cannot solve protected outer guesses accidentally;
- constructor-local pattern variables become local rigid parameters and are checked for existential escape;
- constructor predicates are wanteds at construction sites and givens at pattern sites;
- match coverage filters impossible constructors by result-type satisfiability before Maranget usefulness runs;
- or-pattern alternatives with different GADT refinements are rejected for now.

The inference rule follows OutsideIn(X)'s generated `case` shape: a
fresh result variable is shared by all arms, while each GADT arm's
wanteds are solved under its local givens. Talk also adopts the
practical extension discussed in OutsideIn(X) Section 5.6.1: after an
implication has been simplified under its givens, residual constraints
that do not mention constructor-local skolems may float outward. This
accepts useful cases where all branches infer the same result type,
while still rejecting matches whose result would have to be a
refinement-dependent non-principal type.

The goal is not to add a separate wrapper around guessed types. The implementation keeps implication solving precise enough that GADT refinements, expected-type propagation, and existential escape checks have one shared mechanism.

## Deferred

- General first-class existential packages beyond protocol `any P`; the protocol-existential surface and implicit-pack no-upcasting guard are implemented in ADR 0003.
- Rank-n eliminators/continuations for consuming existentials without packaging.
- Disjunctive refinement contexts for or-patterns.
- Principal-type inference for matches whose result genuinely depends on different constructor refinements.
