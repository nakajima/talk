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
unknowns and emits constraints relating them:

- `Eq(a, b)` — these two types must unify.
- `EffEq(a, b)` — two effect rows must unify.
- `Conforms { ty, protocol, assoc }` — `ty` must conform to the
  protocol, with the given associated-type bindings.
- `HasMember { receiver, label, member }` — the receiver type has a
  member named `label` whose type is `member`.

(`constraint.rs` defines these; each carries an origin — the AST node
and the reason it was emitted — so errors point at real source.)

The solver then works the constraint set to a fixed point. The reason
for the split is that constraints arrive in source order but their
information flows in every direction: `let xs = []` followed fifty
lines later by `xs.push(1)` checks fine because the element-type
variable stays open until the push constrains it. The solver also gets
to apply *global* policy — what to do with constraints that can't make
progress — in one place instead of scattered through the AST walk.

The remaining files: `ty.rs` is the type representation and `Scheme`
(a polymorphic signature: quantified parameters, their protocol
bounds, carried member constraints, and a body type); `catalog.rs` is
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
7. **Finalize.** Everything the checker stores — node types, schemes,
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
  protocol bounds on the quantified parameter (`<T0: Showable>…`).
- `HasMember` on a group-owned variable is held and attached to the
  scheme (next section).
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
variables replace the quantified parameters, bounds are re-emitted as
new conformance constraints, and — crucially for this compiler — the
chosen substitution is **recorded in a table keyed by the call's AST
node**. After solving, that table says "at this call, T0 = Int". The
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
binding's scheme as a `MemberConstraint`. So

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
on quantified parameters become bounds in the scheme and are checked
at instantiation against the catalog's conformance rows; associated
types are carried as bindings on the bound and as projections
(`T.Element`) that reduce once `T` is known. A projection whose base
never resolves in its group floats, like any other stuck constraint.

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

The source comments cite chapter and verse; the map: the
generate/solve split, floating, and group-at-a-time scoping is
OutsideIn(X) (Vytiniotis, Peyton Jones, Schrijvers & Sulzmann, JFP
2011). Level-based generalization is Rémy's. The binding-group
treatment and the restricted-group rule follow *Typing Haskell in
Haskell* (Jones, 2000) §11.6.2; the value restriction is Wright
(1995). Record rows are Leijen (2005) and Gaster & Jones (POPL 1996);
effect rows are Koka (Leijen, POPL 2017). Protocols-as-predicates
with witnesses is Wadler & Blott (1989) via Hall et al. (TOPLAS
1996); associated types are Chakravarty et al. (ICFP 2005).
Schemes that carry member constraints are qualified types (Jones,
1994), with `HasMember` from Gaster & Jones; the refusal to pick among
overlapping providers is that book's coherence argument (§2.4).
