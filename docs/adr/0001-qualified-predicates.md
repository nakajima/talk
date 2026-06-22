# ADR 0001: Qualified predicates and declaration `where` clauses

## Status

Accepted.

## Context

Talk already has several predicate-like mechanisms in the type checker:

- protocol conformance constraints (`T: P`);
- associated-type projections and bindings;
- inferred `HasMember` constraints;
- equality and effect-row constraints in the solver;
- hooks for GADTs through implication constraints and variant result types.

These mechanisms were not represented as one qualified context. Generic parameter bounds lived on `SchemeParam`, inferred member constraints lived separately on `Scheme`, conditional conformances had their own context shape, and same-type constraints such as `where T == U` had no principled home.

The language goal is a coherent predicate system, not a syntax-only feature bolted onto generics.

## Research basis

Sources directly checked for this ADR/refactor; PDFs are mirrored under `papers/`:

- Jones, *A Theory of Qualified Types* (ESOP 1992; revised SCP version): qualified types have the shape `forall t. P => type`, with predicates restricting instantiation and an evidence interpretation for overloading.
- Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann, *OutsideIn(X): Modular type inference with local assumptions* (JFP 2011): the solver architecture separates an underlying constraint domain X from originated wanteds/givens and implication constraints.
- Wadler and Blott, *How to make ad-hoc polymorphism less ad hoc* (POPL 1989), plus Hall/Hammond/Peyton Jones/Wadler, *Type Classes in Haskell*: protocol conformance is the local language analogue of class predicates with statically selected evidence.
- Chakravarty, Keller, and Peyton Jones, *Associated Type Synonyms* (ICFP 2005): associated types are type-level functions/projections, and useful signatures need equality constraints such as `Elem c = Int`.
- Gaster and Jones, *A Polymorphic Type System for Extensible Records and Variants* (NOTTCS-TR-96-3, 1996), and Leijen, *Extensible Records with Scoped Labels* (TFP 2005): member/row constraints belong in the same qualified predicate space rather than as ad-hoc side channels.
- Leijen, *Koka: Programming with Row-Polymorphic Effect Types* (MSR-TR-2013-79, 2013): effect rows should be represented as first-class row constraints now, even if source effect predicates come later.
- Jones, *Typing Haskell in Haskell*, section 11.6: binding-group inference splits predicates into deferred and retained predicates; retained predicates become the inferred qualified context.
- Jones, *Simplifying and Improving Qualified Types* (YALEU/DCS/RR-1040, 1994): improvement is a justified substitution from predicate satisfiability information, not a guess.

## Decision

Talk's type system uses one origin-free predicate language for qualified contexts, wanteds, givens, schemes, and GADT refinements. A wanted is a predicate plus a `CtOrigin`; an implication carries given predicates and wanted predicates.

The internal predicate language is kind-aware:

- type equality;
- effect-row equality;
- record-row equality;
- protocol conformance;
- internal `HasMember`.

Evidence is static and erased for now. The lowerer continues to rely on monomorphization and concrete witness selection instead of runtime dictionaries.

Source-level declaration `where` clauses lower into this predicate language. Inline generic bounds remain syntactic sugar and lower into the same context. Protocol composition uses `&`; separate where predicates use `&&`. The implemented v1 covers functions, methods, protocol requirements, structs, enums, extends, effects, associated types, and protocols.

Associated-type protocol applications are semantic sugar for conformance plus equality predicates. For example, `T: Iterator<Element>` means `T: Iterator` and `T.Element == Element` after the projection has a known protocol owner.

## Nominal well-formedness

A `where` clause on a nominal type is a well-formedness condition on the type application, not a constructor-only hidden constraint. This is deliberately not Haskell's deprecated datatype-context behavior; the GHC User's Guide describes datatype contexts as adding constraints to constructors and calls the feature a misfeature.

For example:

```talk
struct Box<T> where T: Showable {
    let value: T
}
```

means `Box<A>` is well-formed only when `A: Showable`, and that predicate is available while checking `Box` members. Every formation of `Box<A>` must satisfy the stored well-formedness predicates.

## `Self` in predicates

`Self` is valid in declaration predicates.

- In a protocol, `Self` is the protocol self parameter.
- In a struct or enum, `Self` is the nominal applied to its declared parameters.
- In an extend block, `Self` is the extend head.

`protocol P where Self: Q` entails the same superprotocol relationship as `protocol P: Q`. If both spellings state the same fact, the checker should warn only for the exact duplicate fact and prefer the existing superprotocol spelling.

Protocol refinements are inherited transitively. If `IntIterable: Iterable where Self.Element == Int`, then `T: IntIterable` entails both `T: Iterable` and `T.Element == Int`.

## Ambiguity and satisfiability

Every source `where` predicate must mention a declaration-scoped type variable or `Self`; `where Int: P` is not a place to assert global facts.

Predicate-constrained generics must be determined by the declaration's exposed type, `Self`, nominal application parameters, or equalities that connect them to determined variables. Ambiguous constrained declarations such as `func make<T>() -> Int where T: P` are rejected at the declaration site. A future metatype/type-witness API, such as `sizeOf(T.self)`, is the intended escape hatch for APIs selected by type rather than value.

Abstract predicates are allowed as assumptions. Concrete predicates forced by equality givens should be checked and rejected early when unsatisfied.

## Source syntax boundaries

Declaration-level `where` clauses are accepted for the full v1 set of declaration forms with type context: functions, methods, protocol requirements, structs, enums, extends, effects, associated types, and protocols.

`HasMember` is an internal predicate and may be rendered in inferred schemes, but there is no source syntax for member predicates yet.

Effect-row predicates are part of the internal predicate framework so effect polymorphism does not require a second architecture later. Source `where` syntax does not expose effect predicates initially.

## Implementation plan

1. Introduce `Predicate` and move schemes toward `forall params. predicates => type`. Done.
2. Migrate existing generic bounds and inferred member constraints to `Scheme.predicates` while preserving existing syntax. Done.
3. Add solver givens and equality canonicalization for declaration `where` givens. Done for v1; a fuller inert-set implementation remains future solver engineering.
4. Enforce nominal well-formedness predicates at every nominal type application. Done.
5. Add syntactic `where` AST nodes and lower them after name resolution. Done for the full v1 declaration set.
6. Add redundancy warnings for exact canonical duplicate facts after desugaring. Done for duplicate source predicates.
7. Extend the same predicate machinery for GADT constructor and match-arm refinements. Done via ADR 0002.
