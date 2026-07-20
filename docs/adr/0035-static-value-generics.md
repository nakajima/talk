# 0035 - Static value generics with a restricted index language

Status: accepted; implemented (2026-07-19)

## Context

Talk generics range only over types. This prevents types and functions from
expressing statically known values that affect representation or API contracts,
such as a matrix's dimensions, an inline buffer's capacity, or a vector's lane
count. Encoding each value as a distinct marker type would add boilerplate,
duplicate value- and type-level concepts, and make inference indirect.

The feature commonly called "const generics" combines four separate concerns:

1. which values may participate in types;
2. which computations may run while checking types;
3. how the checker proves equality and ordering between symbolic value
   expressions; and
4. how value-parameterized code is represented and specialized.

Treating all four as unrestricted compile-time execution would make type
checking depend on arbitrary Talk programs. General program equivalence is
undecidable, compile-time execution can fail to terminate, and generic errors
would move from declaration checking to concrete instantiation. At the other
extreme, allowing only a bare parameter such as `N` in a type is predictable
but fails as soon as an API needs `N + 1`, `Rows * Stride`, or a non-empty
constraint.

Talk already has the right integration points for a middle course:

- generic declarations and recorded per-use substitutions;
- one qualified predicate language for schemes, wanteds, givens, nominal
  well-formedness, and GADT refinements (ADR 0001);
- separate constraint generation and solving;
- frontend-selected meaning consumed by a whole-program monomorphizing backend
  (ADR 0034); and
- first-class protocol existentials as an explicit, evidence-carrying runtime
  boundary (ADR 0003).

## Research basis

The design follows the restricted-index tradition rather than template
metaprogramming or full dependent type theory:

- Xi and Pfenning, *Eliminating Array Bound Checking Through Dependent Types*
  (PLDI 1998), and *Dependent Types in Practical Programming* (POPL 1999):
  ordinary programs are indexed by a separate, decidable constraint domain;
  checking produces arithmetic obligations and index evidence erases.
- Hughes, Pareto, and Sabry, *Proving the Correctness of Reactive Systems Using
  Sized Types* (POPL 1996): static size indices can express useful invariants
  without making all terms available to the type language.
- Freeman and Pfenning, *Refinement Types for ML* (PLDI 1991), and Rondon,
  Kawaguchi, and Jhala, *Liquid Types* (PLDI 2008): useful value constraints
  require an intentionally bounded logic and predictable entailment.
- Cardelli, *Phase Distinctions in Type Theory* (1988), and Davies and
  Pfenning, *A Modal Analysis of Staged Computation* (POPL 1996): compile-time
  and runtime computation need an explicit phase boundary.

Existing language designs reinforce the boundary chosen here. Rust's stable
const generics are predictable but largely prohibit symbolic arithmetic in
types. C++ templates, D templates, and Zig `comptime` admit much broader
compile-time computation but pay in instantiation behavior, compiler work, and
diagnostics. Chapel's `param` parameters are the closest direct industrial
model. GHC type-level naturals and full dependent languages demonstrate the
need for explicit existential packaging when an index is known only at
runtime.

## Decision

### 1. Mixed type and static value parameters

Generic parameter lists may contain both type parameters and static value
parameters. A static parameter is introduced with `static` and has a declared
value type:

```talk
struct InlineArray<Element, static Count: Int> {
    // compiler-known inline representation
}

func append<static Left: Int, static Right: Int, Element>(
    lhs: [Element; Left],
    rhs: [Element; Right],
) -> [Element; Left + Right] {
    // ...
}
```

`static` denotes phase, not storage duration or mutability. Static parameters
are immutable. Their names follow Talk's generic-parameter convention and must
begin with an uppercase letter; `static N: Int` is valid and `static n: Int`
is rejected. Existing `static func` syntax continues to mean a function on a
type or protocol namespace; its declaration position distinguishes it from a
static generic parameter.

Every declaration form that already accepts generic parameters uses the same
mixed parameter representation. This includes functions, nominal types,
protocols, effects, enum cases, and extensions. The feature does not introduce
associated static values; an `associated value` facility requires a separate
decision.

A generic argument position is interpreted according to its declared
parameter. For example, `[Int; 4]` supplies the type `Int` and static value
`4`. Defaults are permitted when the default is a valid static
expression and mentions only earlier parameters.

### 2. Initial static value domain

The initial domain is deliberately structural and target-independent:

- nonnegative `Int` values;
- `Bool`; and
- cases of fieldless enums.

Talk has no `Nat` value type, so the source spelling is `static N: Int`;
well-formed static arguments occupy the nonnegative subset of Talk's signed
64-bit `Int` range. This is a static-parameter domain restriction, not a new
runtime numeric type. Negative static arguments and a general signed static
integer domain are deferred.

Payload enums, `Float`, strings, characters, pointers, records, arrays,
closures, existential packages, and host values are not static generic
arguments in this version. Their equality, representation, or provenance
would enlarge the feature without serving the initial size-and-shape use case.

Each static `Int` parameter contributes an implicit `0 <= N` given while its
declaration is checked. Forming an application emits the corresponding
nonnegativity wanted for every integer argument. Index expressions may
therefore become negative while solving, but any expression used as a generic
argument must be proven nonnegative; for example, `N - 1` requires a context
that proves `0 < N`.

### 3. A separate, total static expression language

Static generic expressions are not arbitrary Talk expressions. The initial
integer index language contains:

- integer literals and static parameters;
- parentheses;
- addition and subtraction; and
- multiplication by an integer literal.

Boolean and fieldless-enum static expressions contain literals/cases and
static parameters. Equality is available for every static domain. Ordering is
available for integer expressions.

The following are intentionally outside the initial language:

- calls to user-defined or standard-library functions;
- division, remainder, exponentiation, shifts, and bitwise operations;
- multiplication of two symbolic expressions;
- allocation, mutation, effects, I/O, reflection, and macros; and
- conditionals or pattern matching that construct types.

Closed expressions evaluate during checking. Open integer expressions
normalize to affine forms. Static arithmetic has mathematical-integer
semantics during normalization; once an expression becomes a concrete `Int`,
its result must fit Talk's signed 64-bit range. Compiler arithmetic therefore
cannot overflow, and normalization cannot change a result by introducing
machine overflow.

A later compile-time execution feature may produce a closed static value, but
it will not change the symbolic equality rules in this ADR. Arbitrary function
bodies do not become part of definitional equality.

### 4. Canonical equality and a bounded arithmetic theory

The checker canonicalizes affine integer expressions. Consequently, these
pairs are definitionally equal without user proofs:

```text
N + 1              1 + N
2 * N               N + N
Rows * 4 + 4        4 * (Rows + 1)
```

Type identity includes the canonical static arguments. Closed expressions are
reduced before identity, so `[Int; 2 + 2]` and `[Int; 4]` are the same type.

Qualified contexts gain origin-free static predicates alongside the existing
type, row, effect, conformance, and member predicates:

- static equality for values in the same static domain;
- integer less-than; and
- integer less-than-or-equal.

Source `where` clauses use the existing `&&` conjunction:

```talk
func first<static Count: Int, Element>(
    values: [Element; Count],
) -> Element where 0 < Count {
    // ...
}
```

These predicates participate in schemes, wanteds, givens, nominal
well-formedness, and implication constraints exactly like the predicate forms
owned by ADR 0001. Arithmetic evidence is compile-time evidence and erases.

Entailment is limited to the selected quantifier-free linear integer domain.
The implementation must be deterministic, resource-bounded, and in-tree; this
ADR does not authorize an external SMT dependency. If the checker cannot prove
an obligation within the supported theory or its resource limit, it rejects
the program with an unproven-static-predicate diagnostic. It never assumes the
predicate.

Nonlinear facts, user-function equations, disjunction, and induction require
an explicit future extension rather than solver heuristics.

### 5. Declaration checking remains separate from instantiation

A generic body is checked once with its static parameters rigid and its
`where` predicates available as givens. It is not deferred until every
concrete instantiation. Operations in the body must follow from the declared
static theory and ordinary generic bounds.

Inference may obtain a static argument from an expected or actual type:

```talk
func count<static N: Int, Element>(
    values: [Element; N],
) -> Int {
    N
}
```

A call with `[Byte; 4]` infers `N = 4`. Inference solves only static
equalities with a unique solution in the supported affine theory. Ambiguous
or underdetermined arguments require an explicit generic argument. The
checker does not inspect an ordinary runtime argument's value to infer a
static parameter.

Static parameters follow the existing determined-variable rule: they must be
determined by the exposed declaration type, its owner application,
static equalities to determined parameters, or an explicit generic argument.
No unresolved static metavariable may survive finalization.

### 6. Static values may be used at runtime

A static parameter may appear as an ordinary value in its declaration body.
The backend substitutes its concrete value during specialization:

```talk
func width<static N: Int>() -> Int {
    N
}
```

Using `N` in an ordinary `if` does not create dependent control-flow typing.
Both branches are checked under the same generic context, although a backend
may remove the dead branch after specialization.

There is no implicit conversion in the other direction. A runtime `Int`
cannot instantiate a static parameter, even if the value happens to be
constant during one execution.

### 7. Runtime-unknown indices require a distinct abstraction

This ADR does not add dependent pairs or an existential over static values.
Code that reads a runtime size uses a dynamic collection. Converting a runtime
size into "some `N` and an `[T; N]`" requires an explicit
existential/reification design in a later ADR; the compiler will not generate
an unbounded runtime dispatch over static instantiations.

Likewise, knowing a container's static length does not by itself prove that an
ordinary runtime index is in bounds. Bounds-check elimination requires a
bounded-index type, a refinement proven by control flow, or a runtime check.
That is separate from static value parameterization.

### 8. Monomorphization, layout, and coherence

The frontend records static substitutions alongside type substitutions and
publishes only solved, canonical arguments. The ADR 0034 backend specializes
reachable generic bodies over both type and static assignments. Static values
that affect field types or layout therefore produce distinct concrete layouts.

Normalized static arguments are part of nominal type identity, specialization
keys, and any symbol or module identity that crosses a real compilation seam.
An implementation may share machine code between layout-compatible
instantiations, but that is an unobservable optimization rather than a source
semantic distinction.

Static values do not introduce ordered specialization. Existing coherence
rules continue to reject overlapping conformances or extensions; a general
implementation for `[T; N]` and a competing implementation for
`[T; 0]` do not acquire C++-style priority merely because one is
more specific. Any future specialization system needs its own coherence
decision.

Layout formation emits and proves its required predicates, including
representable size/alignment and checked multiplication. A static argument
being a valid nonnegative `Int` does not make every layout derived from it
valid.

## Consequences

- Talk gains direct value-parameterized types and functions without adopting
  arbitrary compile-time metaprogramming.
- Common affine shape relationships are expressible and canonical; users do
  not encounter Rust's bare-parameter-only limitation for `N + 1`-style APIs.
- Type checking and generic diagnostics remain declaration-local.
- The solver grows a second kind of equality term, but not a second constraint
  architecture: static predicates use the qualified context established by
  ADR 0001.
- Concrete static values are target-independent and deterministic. Initial
  integer arguments are nonnegative; pointers, floats, strings, and structural
  object serialization do not become type identity problems.
- Monomorphization can increase compile time and code size for APIs used at
  many static values. Layout-changing instantiations necessarily remain
  distinct; code sharing is an optimization for the others.
- Dynamic and static collection APIs remain visibly different. No runtime
  value is silently promoted into the type system.
- More expressive arithmetic, compile-time functions, associated static
  values, bounded index types, and existential static indices remain separate
  decisions rather than accidental consequences of this feature.

## Implementation sequence

1. Tag scheme and nominal parameters by kind: type or static value of an
   admitted static type. Extend substitutions and canonical specialization
   keys accordingly.
2. Extend parsing, formatting, name resolution, and diagnostics for `static`
   parameters, mixed generic arguments, and static expressions.
3. Add the typed static-expression representation and affine normalizer. Keep
   it separate from the ordinary expression AST after resolution.
4. Add static predicates to the shared qualified constraint language and
   implement deterministic linear-integer entailment, implication handling,
   ambiguity checks, and source origins.
5. Extend catalog well-formedness, scheme instantiation, per-use substitution
   recording, hover/rendering, and module identity with canonical static
   arguments.
6. Extend whole-program specialization and layout validation to consume the
   frontend's solved static substitutions.
7. Add focused language facilities such as fixed-size inline storage in a
   separate decision after the generic mechanism is complete; do not hide a
   second const-generic implementation inside a builtin collection.

Each step must reject unsupported static forms rather than lowering them as
ordinary runtime expressions or carrying unresolved symbolic values into the
backend.

## Alternatives rejected

### Arbitrary compile-time Talk evaluation

This is the C++/D/Zig direction. It is powerful, but it couples type identity
to evaluator termination, effects, compiler resource limits, and program
equivalence. Talk may add explicit compile-time execution later, but it will
produce closed arguments at this boundary rather than define symbolic type
equality.

### Bare static parameters with no symbolic arithmetic

This is close to Rust's stable minimum. It makes the first implementation
smaller but leaves basic APIs such as append, grow, and matrix composition
inexpressible. Affine normalization is included in the semantic foundation
rather than added later with incompatible equality rules.

### Full dependent types

Allowing arbitrary runtime terms in types would require dependent elimination,
proof terms, totality policy, erasure rules, and existential indices. That is a
different language design, not a larger version of this feature.

### Type-level encodings and singleton witnesses

Haskell-style promoted naturals and singleton dictionaries can encode the
feature without mixed generic parameters, but duplicate ordinary values at the
type level and expose representation machinery to users. Talk will represent
static values directly.

### General SMT-backed refinements

An SMT solver would admit a larger predicate language but introduce external
solver behavior, less predictable diagnostics, and a substantially larger
trusted boundary. The initial affine domain covers the motivating shape use
cases with an in-tree decision procedure.

### Runtime discriminants

Ada-style runtime discriminants permit runtime-dependent representation, but
they do not provide the static type identity and whole-program specialization
chosen here. Dynamic-size values remain dynamic collections in Talk.
