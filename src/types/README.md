# How the type checker works

This directory turns a parsed, name-resolved program into answers: the
type of every expression, the signature of every function, which
declaration each member use lands on, and what to specialize where.
The lowerer, the LSP, and the REPL all consume those answers; nothing
downstream re-derives types.

The reader this document assumes: you know what a type variable and
unification are, you've seen Hindley–Milner-style inference described,
but you haven't read the papers this implementation follows. Terms
specific to this codebase are introduced as they come up.

## Architecture: generate constraints, then solve them

The checker is split into a **constraint generator** (`generate.rs`)
and a **solver** (`solve.rs`). The generator walks the AST and never
decides anything on the spot; it allocates type variables for the
unknowns and emits **wanteds**: an origin-free predicate plus a source
origin for blame.

The predicate language is shared by schemes, wanteds, and future givens:

- `TypeEq(a, b)` — these two types must unify.
- `EffectEq(a, b)` — two effect rows must unify.
- `RowEq(a, b)` — two record rows must unify.
- `Conforms { ty, protocol }` — `ty` must conform to the protocol.
- `HasMember { receiver, label, member }` — the receiver type has a
  member named `label` whose type is `member`.

`constraint.rs` contains the originated solver forms. `ty.rs` contains
`Predicate`, because schemes, conformance contexts, and future GADT
givens store predicates without source origins.

The solver then works the constraint set to a fixed point. The reason
for the split is that constraints arrive in source order but their
information flows in every direction: `let xs = []` followed fifty
lines later by `xs.push(1)` checks fine because the element-type
variable stays open until the push constrains it. The solver also gets
to apply *global* policy — what to do with constraints that can't make
progress — in one place instead of scattered through the AST walk.

The remaining files: `ty.rs` is the type representation and `Scheme`
(a polymorphic signature shaped as `forall params. predicates => type`);
`catalog.rs` is
the table of declared things (structs with fields/methods, enums with
variants, protocols with requirements, conformances with witnesses,
effects); `output.rs` is `TypeOutput`, the checker's public product;
`error.rs` the error enum and messages.

## The pipeline, phase by phase

`check_program` in `generate.rs` runs:

1. **Declaration collection.** Structs, enums, protocols, and effects
   register their shapes in the catalog; member functions get
   placeholder signatures so uses can reference them before their
   bodies are checked. `extend` blocks are collected for later.
2. **Binding groups, in dependency order.** Top-level functions and
   `let`s are partitioned into strongly connected components of the
   "who references whom" graph — mutually recursive functions share a
   group; everything else is its own group — and the groups are
   checked in reverse topological order, so a binding's dependencies
   always have finished schemes before its own group starts.
3. **Extend bodies**, each as its own mini-group. A witness body is
   checked against the protocol requirement's declared signature, and
   any associated types the solver inferred along the way are written
   back into the conformance row (so an unannotated witness still
   pins, say, `Iterator.Element`).
4. **Protocol default bodies**, checked once, generically: `Self` is a
   rigid parameter bounded by the protocol itself, so a default can
   call the protocol's other requirements but can't assume any
   concrete receiver.
5. **Top-level statements**, in source order, against the finished
   schemes.
6. **The final solve.** Constraints that earlier phases couldn't
   resolve locally (see "floating" below) get one last pass with
   defaulting enabled; whatever still survives becomes an error.
7. **Match coverage** (`exhaustiveness.rs`). With every scrutinee's
   type now solved, each `match` is checked two ways: does some value
   of the scrutinee's type reach no arm (an error, reported with
   example values like `.blue` or `.some(false)`), and can any value
   reach each arm (an arm shadowed by the ones above it is a
   warning). Both are the "usefulness" question from Maranget's
   *Warnings for pattern matching* (JFP 2007), and the matrix
   machinery is the same shape the lowerer's decision-tree compiler
   uses — this pass answers "is anything missed?", that one picks
   which tests to emit.
8. **Finalize.** Everything the checker stores — node types, schemes,
   instantiation tables — gets its solved variables substituted in
   ("zonked") and is packaged into `TypeOutput`.

## Inside one binding group

Each group is checked at a fresh **level**. Levels are the standard
trick for sound generalization: every type variable is tagged with the
level that created it, and when the group ends, only variables at the
group's level or deeper may be generalized. A variable from an
enclosing scope (lower level) might still be constrained by code the
checker hasn't reached, so it must not be quantified here.

The sequence: allocate a monomorphic skeleton variable per binder;
infer every body, equating each result with its binder's skeleton
(this is why recursion inside a group is monomorphic — a recursive
call sees the skeleton, not a scheme); run the solver; then decide
whether the group **generalizes**:

- Generalization is allowed only if every binder's right-hand side is
  a syntactic value (a function literal, a constant — something whose
  evaluation can't observe or produce mutable state). One non-value
  binder makes the whole group monomorphic. This is the classic value
  restriction; without it, a generalized mutable cell could be written
  at one type and read at another.
- If the group generalizes, every type variable still unsolved at the
  group's level becomes a quantified parameter. `func id(x) { x }`
  ends up `<T0>(T0) -> T0` with nobody writing a generic.
- Annotated bindings skip generalization and take exactly their
  annotation; declared generics (`func f<T>(…)`) become quantified
  parameters directly.

Local `let`s inside function bodies never generalize — each local has
one monomorphic type. That's a deliberate restriction (GHC's
MonoLocalBinds): generalizing locals under an open constraint set
produces schemes whose meaning shifts with inference order, and the
papers this design follows concluded it isn't worth it.

## Nominal types in the group graph

A struct or enum splits into two halves that the checker treats very
differently. Its **shape** — field names and types, variant payloads,
which methods exist and their declared signatures — goes into the
catalog during phase 1, before any group runs, so any code anywhere
can mention `Person` or emit a `HasMember` about `getAge` regardless
of order. Its **member bodies** are ordinary code that needs
inference, so the declaration itself becomes a node in the dependency
graph, right alongside the top-level `let`s and functions, and its
methods and inits are checked inside whatever group it lands in.

Edges are computed by scanning bodies for references to other
top-level binders:

- A method or init body that calls a global function puts an edge
  from the struct's node to that function's node — so the struct's
  group runs *after* the function has a finished scheme.
- Any expression that names the type (`Person(age: 123)` — the
  constructor is a reference like any other) gets an edge to the
  struct's node — so users of the type run after its members are
  checked.
- A method that calls a global which itself constructs the struct is
  a cycle; the SCC computation puts both in one group and they're
  checked together against each other's skeletons, like any mutual
  recursion.

When a group containing a nominal is checked, member skeletons are
created first (queued ahead of body inference), so methods, inits,
and `let`s in the same group can reference one another freely. While
member bodies run, `self` is bound to the owner's type with its
declared type parameters held rigid — a method body can't accidentally
specialize its own struct. Each member then generalizes into its own
scheme: a method's quantified parameters are the generics it declared
itself; the owner's parameters stay rigid in the scheme and are
filled in per call site from the receiver's type arguments (the
lowerer calls this owner-theta).

Order still can't always be perfect — a function whose parameter is
only *constrained* to have a member (`func g(aged) { aged.getAge() }`)
has no name-level reference to `Person`, so no edge exists and g's
group may run first. Two mechanisms make that safe. A member
constraint that resolves to a method whose signature is still an
unsolved variable (its group hasn't run) is left stuck and floats to
the final solve rather than unifying against a half-baked signature.
And a reference to a binder whose group hasn't run yet gets a fresh
variable at the *outer* level, which the referencing group
conservatively refuses to generalize — wrong order degrades to less
polymorphism, never to unsoundness.

One asymmetry to know about: the edge scan currently walks struct
member bodies but not enum member bodies, so an enum whose method
calls a global function gets no edge to it and may be checked first.
The conservative fallbacks above keep that correct, but the enum's
group can monomorphize a generic function it uses out of order —
struct and enum bodies should get the same scan.

`extend` blocks sit outside the group graph entirely: they're checked
after all groups (phase 3), because nothing needs a witness body's
inferred type earlier — member dispatch on a conformance goes through
the protocol requirement's declared signature, which the catalog has
had since phase 1.

## The solver loop

`Solver::solve` runs a worklist. Equalities unify immediately
(union-find over variables, with an occurs check — unifying a variable
with a type containing itself is reported as an infinite type, not
looped on). Conformance and member constraints try to discharge
against the catalog; ones that can't make progress yet — say, a member
constraint whose receiver is still a bare variable — are parked as
**stuck**.

When the queue drains, stuck constraints get another chance if any
unification happened since they were parked (a generation counter
tracks this — new information may unstick them). When that stops
helping, the solver runs **improvement**: committing choices that are
forced or deliberately chosen as policy rather than derived:

- A member label that no struct, enum, or protocol declares anywhere
  must be a record field, so the receiver is unified with an open
  record row containing that field (this is what makes
  `func f(r) { r.a }` infer a row-polymorphic record type).
- A label owned by exactly one *protocol* dispatches through that
  protocol: the receiver picks up a conformance bound but stays a
  variable, so polymorphism survives.
- A label owned by one *nominal* type, or by several owners, is left
  alone here — see "member constraints ride schemes" below.

Improvement may enable more solving, so the loop repeats until nothing
moves. Then the endgame: stuck constraints become **residuals**
returned to the caller rather than errors, because a constraint that's
unsolvable *now* may be solvable *later* — its variables can be
touched by sibling groups or by top-level statements. `check_group`
triages residuals:

- Variable-headed `Conforms` on a variable the group owns become
  conformance predicates on the quantified parameter (`<T0: Showable>…`).
- `HasMember` on a group-owned variable is held and attached to the
  scheme as a predicate (next section).
- Everything else **floats**: it's pushed onto a deferred list that
  the final solve (phase 6) retries with the whole program's
  information available. Only the final solve runs with `defaulting`
  on, which enables one last improvement rule: a still-unknown
  receiver whose member label is owned by exactly one nominal type
  commits to that type. Committing earlier would be wrong — it would
  monomorphize functions that deserve to stay generic — but at the
  very end, guessing the unique owner beats erroring.

## Instantiation, and how the lowerer specializes

Every use of a polymorphic binding instantiates its scheme: fresh
variables replace the quantified parameters, predicates are re-emitted
as new wanteds, and — crucially for this compiler — the chosen
substitution is **recorded in a table keyed by the call's AST node**.
After solving, that table says "at this call, T0 = Int". The
lowerer reads it to stamp out one specialized copy of the function per
distinct type assignment, so generated code is fully monomorphic: no
boxing, no runtime type tags, field offsets computed per
specialization.

Row-polymorphic signatures participate too: the recorded entry for a
row parameter is the concrete record row, and `Ty::substitute` splices
it into the signature so each specialization knows its exact field
layout.

## Records and effects are rows

A record type is a sorted list of `label: type` fields plus an
optional **tail**: either closed (exactly these fields) or a
variable/parameter meaning "and possibly more". Unifying two rows
matches fields by label and unifies the leftovers with the tails.
`func f(r) { r.a }` therefore infers "r is a record with `a: T`, plus
unknown other fields" — any record with an `a` is accepted, and each
call site fills in what the other fields actually are.

Effects use the same row machinery with effect names instead of
fields. Every function type carries the row of effects its body may
perform; an open tail means "plus whatever my function-typed arguments
perform", which is how higher-order functions stay effect-polymorphic
without annotations. A handler removes its effect from the row of the
code it wraps. A *closed* effect annotation (`func f() 'io -> …`) is
checked as an exact upper bound at the declaration: performing
anything not listed is an error there, not at the call.

## Qualified predicates and declaration `where`

Schemes have one qualified context: `forall params. predicates =>
type`. Inline bounds such as `<T: Showable>` lower to the same predicate
language as inferred constraints and declaration-level `where` clauses.
Predicates are origin-free; wanteds add source origins for blame.

Declaration `where` clauses are supported for functions, methods,
protocol requirements, structs, enums, extends, effects, associated types,
and protocols. Function, method, and requirement clauses parse after the
signature; extend clauses parse after the conformance list; nominal and
protocol clauses parse before the body; effect clauses parse after the
operation return type; associated-type clauses parse after the associated
declaration. They use `&&` between predicates, use `&` for protocol
composition inside one conformance predicate, and lower after name
resolution into the same predicate language. Function/method clauses become
scheme predicates plus local erased givens while the body is checked.
Extend clauses become the conditional-conformance context emitted as
wanteds when the conformance is used. Nominal clauses are stored as
well-formedness predicates checked at every nominal type application.
Protocol clauses become inherited refinements. Effect clauses constrain each
perform-site instantiation, and associated-type clauses add bounds on the
associated parameter. Protocol-application sugar such as `T:
Iterator<Element>` lowers to `T: Iterator` plus `T.Item == Element`.
Predicate-constrained generics must be determined by the declaration's
exposed function type, `Self`, nominal parameters, or by same-type
predicates that connect them to determined parameters; `func make<T>() ->
Int where T: P` is rejected as ambiguous.

A nominal `where` clause is a **well-formedness predicate** on the type
application, not a constructor-only hidden constraint. `struct Box<T> where T:
Showable` means every `Box<A>` formation must prove `A: Showable`; it
does not merely add a hidden constraint to constructors.

The predicate framework is kind-aware from the start, including type,
row, and effect equalities, so future effect polymorphism and GADT
refinements use the same architecture instead of a parallel constraint
system. Runtime evidence is still erased: monomorphization and concrete
witness selection remain the backend story for now.

## Member constraints ride schemes

`x.m` emits `HasMember`. When the receiver's head type is known, the
solver discharges it directly: struct/enum field or method (the
method's `self` parameter unifies with the receiver, and what's left
of the signature is the member's type); record (becomes a row
constraint); bounded generic parameter or associated type (dispatches
through the bound protocol's requirement); concrete type with
conformances (dispatches through the conformance's witness).

When the receiver is still a variable at the end of a group, the
constraint is *held* through generalization and attached to the
binding's scheme as a `Predicate::HasMember`. So

```talk
func g(x) { x.go() }
```

gets the scheme `<T0, T1>(T0) -> T1 where T0.go: () -> T1` — a
qualified type. Each instantiation re-emits the constraint with the
call's fresh variables substituted in, and it discharges against that
call's concrete receiver. Two unrelated structs that both define
`go()` can flow through the same `g`; the lowerer re-resolves the
member by label inside each specialized copy, so each gets the right
method statically. A record with a `go` field of function type
satisfies the same constraint — the qualification is structural.

Resolution refuses to guess in one situation: a receiver whose
conformances (or a parameter whose bounds) provide the same label
through *several distinct* requirements. Picking one would make the
program's meaning depend on declaration order, so it's an
`AmbiguousMember` error, and the message names the explicit forms —
`Aa.m(…)` / `Bb.m(…)`. Calling a requirement through its protocol's
name (`Aa.m(x)`) is the disambiguation syntax; it's the same
protocol-static dispatch operators desugar to, and the LSP offers the
rewrite as a quick-fix. Requirements shared via protocol inheritance
count once, not as an ambiguity.

## Protocols, witnesses, and associated types

A protocol declares requirements (each a signature over `Self`) and
optionally associated types. A conformance (`extend Int: Showable`)
records a **witness** — the concrete function implementing each
requirement — or falls back to the protocol's default body,
specialized at `Self :=` the conforming type. Conformance constraints
on quantified parameters become predicates in the scheme and are
checked at instantiation against the catalog's conformance rows;
associated types are represented as projections (`T.Element`) that
reduce once `T` is known. A projection whose base never resolves in its
group floats, like any other stuck constraint.

`Showable` is auto-derivable: a struct/enum with no explicit
conformance gets one synthesized structurally, and recursive types are
handled by assuming the conformance while deriving it (otherwise a
recursive enum would recurse forever).

## What comes out

`TypeOutput` carries: per-node types (hover and the REPL), finished
schemes, per-call instantiation tables, member resolutions (which
declaration each resolved member use landed on — unresolved ones are
the scheme-carried constraints the lowerer re-resolves per
specialization), the catalog, and tables the lowerer's effect handling
needs: which functions' calls can abort, handler payload types, which
handlers are self-contained, and display names for rendering.

## Further reading

PDFs for these references are mirrored under `papers/`. Verified during the predicate refactor:

- Qualified schemes and predicate contexts: Mark P. Jones, *A Theory
  of Qualified Types* (ESOP 1992; revised SCP paper).
- Constraint generation/solving with wanteds, givens, implication
  constraints, and ambiguity: Vytiniotis, Peyton Jones, Schrijvers,
  and Sulzmann, *OutsideIn(X): Modular type inference with local
  assumptions* (JFP 2011).
- Binding-group splitting into deferred and retained predicates:
  Jones, *Typing Haskell in Haskell*, section 11.6.
- Type classes and evidence/witness translation: Wadler and Blott,
  *How to make ad-hoc polymorphism less ad hoc* (POPL 1989), and Hall,
  Hammond, Peyton Jones, and Wadler, *Type Classes in Haskell*.
- Associated type projections and equality constraints: Chakravarty,
  Keller, and Peyton Jones, *Associated Type Synonyms* (ICFP 2005).
- Row-polymorphic records and `HasMember`-style predicates: Gaster and
  Jones, *A Polymorphic Type System for Extensible Records and
  Variants* (NOTTCS-TR-96-3, 1996), and Leijen, *Extensible Records
  with Scoped Labels* (TFP 2005).
- Effect rows: Leijen, *Koka: Programming with Row-Polymorphic Effect
  Types* (MSR-TR-2013-79, 2013).
- Improvement of qualified predicates: Jones, *Simplifying and
  Improving Qualified Types* (Yale research report YALEU/DCS/RR-1040,
  1994).
- The value restriction used by binding-group generalization: Wright,
  *Simple Imperative Polymorphism* (LISP and Symbolic Computation,
  1995).
