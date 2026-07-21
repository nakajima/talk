# 0036 - Canonical instance heads for extensions

Status: accepted; partially implemented

## Context

Talk uses `extend` for two related declarations:

- protocol conformances, which are top-level axiom schemes;
- inherent members, whose availability is restricted by the extended type.

Both need an **instance head**: a type pattern describing exactly which type
applications the declaration applies to. Examples include:

```talk
extend<T> Array<T>: Iterable {}
extend Range<Int>: Iterable {}
extend<T> Pair<T, Void>: P {}
extend<static N: Int> InlineArray<Int, N>: P {}
```

ADR 0016 already defines a conformance row's logical identity as the full
instance head:

```text
(SelfPattern, ProtocolRefPattern)
```

ADR 0035 makes static arguments part of nominal identity and explicitly rejects
ordered specialization. ADR 0015 requires typing to publish committed dispatch
choices to lowering, with re-selection allowed only where monomorphization
necessarily defers it. ADR 0020 describes conformances as axiom schemes and
requires coherent evidence selection.

The current implementation does not preserve those decisions end to end.

### Syntax conflates declarations with applications

`DeclKind::Extend` currently represents the arguments after the extended name
as `Vec<GenericDecl>`. The same syntax node therefore means either a declaration
or a type argument depending on name lookup. Name resolution contains an
extension-only exception: if a purported generic declaration resolves to a
concrete type such as `Int` or `Void`, it keeps that concrete symbol instead of
declaring a type parameter.

This creates no stable AST invariant. A `GenericDecl` may contain a type
parameter or a builtin/nominal type, and importing a type can change whether a
name is interpreted as a binder or an argument.

### Collection reconstructs an instance head from symbols

Normal type annotations pass through `Elaborator`, which owns generic argument
kinds, static values, defaults, aliases, and nominal well-formedness. Extension
heads bypass it. `CatalogBuilder::register_extend` collects symbols and wraps
every one in `Ty::Param`:

```rust
let self_args = self_params.iter().map(|p| Ty::Param(*p)).collect();
```

For `extend Range<Int>`, name resolution preserves the builtin `Int` symbol and
collection constructs `Ty::Param(Symbol::Int)`. That is a rigid variable whose
symbol happens to be the builtin `Int`, not the concrete type
`Ty::Nominal(Symbol::Int, [])`. It neither unifies with `Int` nor renders as a
valid named parameter, producing diagnostics such as `Builtin(C:1)`.

The previous checker distinguished concrete extension arguments from declared
parameters, but that behavior lived in a checker-local loop. The checker rewrite
lost it because no semantic instance-head interface or source-to-catalog test
owned the rule.

### Catalog identity is too coarse

The catalog currently stores conformances in:

```rust
FxHashMap<(Symbol, ProtocolRef), Conformance>
```

This cannot represent both:

```talk
extend Box<Int>: P {}
extend Box<String>: P {}
```

Both rows have the key `(Box, P)` despite being disjoint full instance heads.
Collection merges rows that collide at this key. `conformances_by_head` loses
the self pattern again by flattening rows to a nominal head and protocol
application.

Inherent extensions have the same problem. `extend_members` stores one member
per `(nominal head, label)`, cannot hold disjoint specialized rows with the same
label, and lookup currently discards whether self-pattern matching succeeded.
Extension-level `where` predicates are not demanded when an inherent member is
used.

### Downstream selection is duplicated and application-insensitive

The solver has structural pattern matching capable of matching concrete,
nested, repeated, and static type patterns, but several callers bypass or
partially reproduce it. The backend additionally flattens facts to
`(head, protocol)`, keeps one `Deinit` row per nominal head, and manually binds
only some top-level parameters while rediscovering witnesses.

A local conversion from a concrete symbol to `Ty::Nominal` would therefore only
move the defect downstream. Concrete instance heads require one representation,
one coherence rule, and one selection interface across collection, solving,
tooling, and lowering.

## Decision

Talk will represent every extension through a canonical, typed instance head.
The compiler will elaborate that head once during catalog collection. All
conformance and inherent-member applicability, overlap, evidence publication,
tooling, and deferred lowering selection will use the same instance-head
semantics.

This is not ordered specialization. Disjoint instance rows may coexist. Any two
rows that can apply to the same fully instantiated key are rejected; declaration
order never supplies priority.

## Source syntax

### Explicit binders precede the extended type

Extension binders use the existing prefix position. The extended type is a
nominal application — a name plus ordinary generic arguments:

```talk
extend<T> Array<T>: Iterable {}
extend<T: Showable> Array<T>: Showable {}
extend Range<Int>: Iterable {}
extend<T> Pair<T, Void>: P {}
extend<static N: Int> InlineArray<Int, N>: P {}
```

The parsed declaration carries the head as a dedicated nominal-application
node, not a general type annotation:

```rust
pub struct TypeApplication {
    pub id: NodeID,
    pub span: Span,
    pub name: Name,
    pub name_span: Span,
    pub args: Vec<GenericArg>,
}

DeclKind::Extend {
    binders: Vec<GenericDecl>,
    head: TypeApplication,
    conformances: Vec<TypeAnnotation>,
    where_clause: Option<WhereClause>,
    body: Body,
}
```

A binder always declares a parameter. A head argument is always a normal
`GenericArg`. The extension-only name-resolution exception that stores concrete
symbols in `GenericDecl` is removed.

The AST shape is the admission rule: an extension head is a name applied to
arguments, never an arbitrary type. Sugar spellings — `[T]`, `[T; N]`, `T?` —
and non-nominal forms — borrows, tuples, function types, `any P` — fail at the
offending token because the head grammar never admits them. There is no
post-parse validation and no reconstruction of what the user typed. Sugar
remains ordinary inside head arguments: `extend<T> Dict<[T]>` is legal because
arguments are ordinary annotations.

The formatter prints the head from `TypeApplication` directly, so annotation
sugar normalization (such as printing `Array<T>` as `[T]`) can never apply to a
head. Core spells Array extensions `extend<Element> Array<Element>`.

The old implicit-binder spelling is migrated:

```talk
extend Array<Element>: Iterable {}
```

becomes:

```talk
extend<Element> Array<Element>: Iterable {}
```

Likewise:

```talk
extend Array<Element: Showable>: Showable {}
```

becomes:

```talk
extend<Element: Showable> Array<Element>: Showable {}
```

A nested `extend Self` continues to inherit its enclosing nominal application.
A binder may occur only in the target protocol or premises, as in:

```talk
extend<T: Into<String>> String: Add<T> {}
```

Arbitrary blanket heads remain rejected:

```talk
extend<T: Iterator> T: Into<Array<T.Element>> {} // rejected
```

Protocol-head axiom schemes remain supported according to ADR 0020:

```talk
extend Iterator: Into<Array<Element>> {}
```

They are distinct from arbitrary parameter-headed extensions.

### A bare generic nominal is an implicit full pattern

In extension-head position only, omitting all arguments from a generic nominal
means a fresh rigid pattern over all of the nominal's declared parameters:

```talk
extend Array {}
```

has the initial head pattern:

```text
forall Element. Array<Element>
```

This permits constrained-extension syntax without inventing names solely to
repeat the nominal declaration:

```talk
extend Array where Self.Element == Int {}
```

Partially supplied argument lists do not acquire this rule. They use ordinary
arity/default rules. The implicit pattern applies only when the argument list is
entirely absent.

## Nominal parameter projections

Declared nominal parameters are named type members of an application. A
projection reduces immediately to the aligned argument:

```talk
Array<Int>.Element       // Int
InlineArray<Byte, 4>.Count // 4
```

Inside an extension, `Self` is the exact instance-head pattern, so:

```talk
extend Array where Self.Element == Int {}
```

starts with `Self = Array<Element>` and `Self.Element` reduces to that rigid
`Element` argument.

Nominal parameter projection is not protocol associated-type projection. It is
an immediate positional reduction, not a `Ty::Proj` requiring conformance
evidence. Protocol associated types retain their existing qualified semantics.

Nominal parameter names occupy the nominal type-member namespace. A nested type
or type alias may not reuse a nominal parameter's name.

Static parameters participate in the same rule. In a static expression,
`Self.Count` reduces to the corresponding static argument and retains its
static kind.

## Head refinement by `where` equalities

Equalities that solve parameters occurring in the self pattern are normalized
into the instance head before catalog insertion. They do not remain as
conditional premises.

Therefore:

```talk
extend Array where Self.Element == Int {}
```

and:

```talk
extend Array<Int> {}
```

produce the same canonical instance head and overlap with one another.

Other examples:

```text
Self.Element == Array<T>  => Array<Array<T>>
Self.Left == Self.Right   => Pair<T, T>
Self.Count == 4           => InlineArray<Element, 4>
```

Head refinement uses kind-aware, occurs-checked pattern equality. It applies the
resulting substitution to the self pattern, target protocol application, and
remaining premises. Solved equalities are removed, unused binders are removed,
and static arguments are canonicalized according to ADR 0035.

A contradictory head equality rejects the extension declaration. An equality
that is not a solvable equation over instance-head parameters remains an
ordinary axiom premise. Premises are not used to establish disjointness:
instances with overlapping heads remain conflicting even if their remaining
premises appear mutually exclusive.

Consequently:

```talk
extend Array where Self.Element: Showable {}
```

remains the conditional rule:

```text
forall Element. Element: Showable => Array<Element>
```

while `Self.Element == Int` changes the head itself.

## Typed representation

The type layer introduces a first-class instance head, conceptually:

```rust
pub struct InstanceHead {
    pub params: Vec<SchemeParam>,
    pub self_pattern: Ty,
}
```

`SchemeParam` preserves the parameter kind required by ADR 0035. An instance
head owns these invariants:

- `self_pattern` is an admitted nominal pattern or the explicit protocol-Self
  form used by protocol-head axiom schemes;
- every rigid parameter in the pattern is declared by the head or is an
  intentional protocol Self/associated parameter;
- builtins, structs, enums, and other concrete types occur as `Ty::Nominal`,
  never `Ty::Param`;
- every argument has the kind declared by its nominal slot;
- static arguments are canonical;
- no unification variable occurs;
- no implicit effect-row argument becomes part of source-level instance
  identity;
- nominal arity, defaults, and well-formedness have been checked.

The module provides the semantic operations, not just fields:

```text
head family
match an actual self type and return one substitution
overlap with another instance head
apply a head substitution
validate portability and parameter closure
```

Pattern matching remains one-way: rigid parameters in the declared pattern bind
to aligned pieces of the actual type. Repeated parameters enforce equality.
Concrete and static arguments compare canonically.

## Elaboration ownership

`Elaborator` gains an instance-head operation used by `CatalogBuilder`. It
reuses ordinary annotation and generic-argument lowering for:

- concrete and nested type arguments;
- declared parameter kinds;
- static arguments and affine normalization;
- defaults;
- transparent aliases where admitted;
- nominal well-formedness obligations.

Instance-head elaboration additionally:

- creates the implicit full pattern for a bare generic nominal;
- keeps declared binders rigid;
- does not append implicit effect-row arguments;
- resolves nominal parameter projections against the exact self pattern;
- absorbs solvable `where` equalities into the head;
- returns remaining predicates as axiom premises.

`CatalogBuilder::register_extend` consumes this typed result. It no longer
constructs `Ty` values from generic symbols.

The collection-to-checking handoff carries the instance head and exact row IDs.
`check_extend` does not rediscover a row through `(head, protocol)` when writing
inferred associated-type bindings.

## Conformance row identity and storage

A conformance row owns its complete semantic conclusion:

```rust
pub struct ConformanceRow {
    pub id: ConformanceId,
    pub head: InstanceHead,
    pub target: ProtocolRef,
    pub context: Vec<Predicate>,
    pub witnesses: FxHashMap<String, Symbol>,
    pub assoc: FxHashMap<Symbol, Ty>,
}
```

`ConformanceId` is stable and module-qualified when it crosses a compilation
seam.

Rows, not a `(Symbol, ProtocolRef)` map entry, are the source of truth. A simple
in-tree row store is sufficient. Derived indexes map:

```text
(head family, target protocol symbol) -> [ConformanceId]
```

The target protocol arguments remain in the row and are matched together with
the self pattern using one substitution. Indexes are rebuilt or restamped on
catalog import/merge and never determine semantics.

The catalog owns a deep conformance interface:

```text
insert a row with coherence checking
find matching rows for a complete wanted
select the unique row and substitution
look up a row by stable ID
enumerate applicable protocol families for member discovery
```

Callers do not inspect row storage or select by catalog order.
`conformances_by_head` is removed or retained only as a private derived index.

### Coherence

Rows overlap when there exists a fully instantiated self type and protocol
application matched by both full conclusions. Remaining contexts do not make
rows disjoint.

Thus these coexist:

```talk
extend Box<Int>: P {}
extend Box<String>: P {}
```

These conflict because Talk has no ordered specialization:

```talk
extend<T> Box<T>: P {}
extend Box<Int>: P {}
```

Duplicate canonical spellings, including a direct concrete head and an
equivalent `Self.Parameter == Concrete` refinement, conflict identically.

Superprotocol rows synthesized from one source conformance retain provenance so
they are not accidentally merged with unrelated rows. Explicit and synthesized
rows obey the same full-head coherence rule.

## Inherent extension rows

Inherent members use the same instance-head semantics. The catalog stores
extension rows rather than one method per nominal-head/label pair:

```rust
pub struct InherentExtensionRow {
    pub id: ExtensionId,
    pub head: InstanceHead,
    pub context: Vec<Predicate>,
    pub members: IndexMap<String, Symbol>,
}
```

A derived index maps `(nominal head, label)` to candidate extension row IDs.
Member lookup matches the actual receiver against every candidate's complete
head. A successful match emits the row's substituted context as wanteds.

Two rows with the same member label may coexist when their heads are disjoint.
Overlapping rows defining the same label are rejected because there is no
priority relation. Overlapping rows with disjoint member labels do not create a
member-selection ambiguity.

Completion and other tooling query applicable inherent rows through the same
catalog interface. They do not enumerate every member attached to a nominal
head regardless of its arguments.

## Solver, evidence, and lowering

The solver consumes canonical rows through the catalog selection interface. It
does not special-case concrete extension arguments; concrete, generic, nested,
repeated, and static patterns are ordinary instance heads.

Selection commits at exactly two points, and nowhere else.

**Typing commits at finalization.** While solving, member dispatch through a
protocol requirement records only the requirement operation: the protocol
application, the requirement symbol, and the receiver type. The solver never
commits a witness mid-solve — receivers may still contain unification
variables, and an early commitment is either wrong or must be re-derived.
After zonking, finalization resolves every requirement operation whose
receiver is concrete through the catalog selector and publishes the committed
row, witness, and row substitution on the node
(`MemberResolution::ViaConformance`). Receivers that remain rigid parameters
stay published as requirement operations
(`MemberResolution::ViaRequirement`).

**Lowering commits at specialization.** A requirement operation inside a
generic body has one witness per instantiation, so no per-node publication can
carry it; the instantiation set only exists as the backend's specialization
worklist drains. When the backend specializes the body, it applies the
instance substitution to the receiver and calls the same catalog selector
typing used. Coherence makes this lookup forced: exactly one row can match, so
the backend dereferences a decision rather than making one. Marker, ownership,
and `Deinit` queries on substituted types are the same deferred lookup.

Lowering owns no selection state and no selection logic. There is no evidence
side-channel: no per-node evidence lists in typed output, no evidence threaded
through specializations, and no backend-owned canonicalization, merging, or
deduplication of selection results. The catalog plus the instance substitution
are the entire evidence channel. This follows ADR 0015: typing publishes every
choice decidable at typing time, and the monomorphization carve-out is a
forced lookup through the shared interface, not a parallel selector.

Application-insensitive backend facts are removed or restricted to rows proven
unconditional for every application. In particular:

- marker and ownership queries receive the complete `Ty`, not only its head;
- `Deinit` selection matches the complete nominal application and may retain
  multiple disjoint rows per nominal family;
- associated bindings come from the selected row and substitution;
- witness lookup matches self and protocol arguments together;
- manual loops that bind only top-level `Ty::Param` patterns are replaced by
  the shared instance matcher.

The backend must not treat the existence of one specialized row as evidence
that every application of the nominal head conforms.

## Diagnostics

Invalid instance heads are rejected at declaration collection with source
spans from the head or refining equality. Diagnostics distinguish:

- invalid extension head shape;
- generic argument arity or kind mismatch;
- contradictory head refinement;
- unresolved or undetermined row parameter;
- overlapping conformance rows;
- overlapping inherent members;
- unsupported arbitrary blanket heads.

An internal/debug validation runs before catalog publication. A malformed value
such as `Ty::Param(Symbol::Int)` in an instance head is an invariant violation,
not a user-facing type mismatch. Valid diagnostics never expose raw forms such
as `Builtin(C:1)` as a purported generic parameter.

## Verification

Tests use the compiler's real interfaces at each seam.

### Syntax and resolution

- Prefix binders and ordinary head arguments parse distinctly.
- A concrete name in a head is never declared as a parameter.
- Sugar spellings (`[T]`, `[T; N]`, `T?`) and non-nominal forms are parse
  errors in head position; sugar inside head arguments parses normally.
- Static and nested generic arguments use ordinary argument syntax.
- Nominal parameter projections resolve to their declaration and support
  navigation.

### Instance-head elaboration

- `extend Range<Int>` produces `Range<Int>`, not `Range<Param(Int)>`.
- A bare generic nominal produces a full rigid pattern.
- `Self.Element == Int` canonicalizes to the same head as `Array<Int>`.
- Repeated, nested, defaulted, and static arguments canonicalize correctly.
- Invalid kinds, contradictions, and escaping variables fail at collection.

### Catalog and solver

- `Box<Int>: P` and `Box<String>: P` coexist and select independently.
- `Box<T>: P` conflicts with `Box<Int>: P`.
- Self and protocol argument patterns share one substitution.
- Conditional contexts are emitted only after the head matches.
- Imported rows preserve identity and selection.

### Inherent members and tooling

- A member on `Box<Int>` is absent from `Box<String>`.
- Disjoint rows may define the same label.
- Overlapping definitions of one label are rejected.
- Extension `where` predicates are demanded at member use.
- Completion filters by the complete receiver application.

### Lowering

- The selected specialized witness is the one executed.
- Deferred generic selection agrees with frontend selection.
- Specialized `Deinit`, marker, and ownership behavior is
  application-sensitive.
- `Range<Int>` iteration passes type checking and agrees across supported
  execution engines.

Module-boundary and catalog-portability tests include concrete, partially
concrete, nested, and static instance heads.

## Implementation sequence

1. Change the extension AST to explicit prefix binders plus a dedicated
   `TypeApplication` head; update parsing, formatting, highlighting, name
   resolution, and source fixtures.
2. Expose nominal parameters as named nominal type members and implement direct
   positional reduction, including static parameters.
3. Introduce `InstanceHead`, its validation, matching, overlap, substitution,
   and focused unit tests.
4. Add instance-head elaboration and head-refinement normalization to
   `Elaborator`; make `CatalogBuilder` consume the result.
5. Replace conformance map identity with stable rows plus derived indexes and a
   catalog-owned selection interface.
6. Replace inherent-member storage with instance rows and enforce contexts and
   overlap through the same semantics.
7. Make `ExtendWork` carry row IDs and update associated-type inference by
   identity.
8. Route solver, member lookup, completion, code actions, import/export, and
   catalog finalization through the new interfaces.
9. Move typing's witness commitment to finalization, publish committed row
   selection per node, and replace backend head-only/manual selection —
   including `Deinit` and ownership queries — with substitute-then-select
   through the shared interface. The backend keeps no selection state.
10. Migrate core/stdlib extension syntax and add source-to-catalog,
    module-boundary, diagnostic, and two-engine tests.

Each step must fail closed. No intermediate phase may interpret a concrete head
argument as a rigid parameter or flatten a specialized row into a universal
head-level fact.

## Consequences

### Benefits

- Extension syntax has one meaning independent of imports and name lookup.
- Instance-head construction, matching, overlap, and validation gain locality in
  one deep module.
- ADR 0016's full conformance identity becomes an encoded invariant rather than
  a convention.
- Concrete, partially concrete, nested, repeated, and static heads use one
  mechanism.
- Conformances and inherent extensions share applicability semantics.
- Tooling and lowering cannot silently disagree with the solver's selected row.
- Future axiom/evidence work from ADR 0020 builds on a stable row identity rather
  than another conformance representation.

### Costs

- Existing generic extension declarations migrate to explicit prefix binders.
- Catalog serialization/import changes because row identity becomes explicit.
- Backend ownership and teardown queries must become application-sensitive.
- Nominal parameter names become part of the type-member namespace.
- The implementation touches several compiler phases because the existing
  coarse representation leaked into each one; this is the complexity the new
  interface is intended to contain permanently.

## Rejected alternatives

### Convert concrete symbols in `collect.rs`

Rejected. Mapping a builtin to `Ty::Nominal` fixes the immediate diagnostic but
leaves conformance-key collisions, unconditional inherent-member visibility,
missing contexts, coarse backend facts, and duplicate selection logic.

### Keep post-name arguments as context-sensitive `GenericDecl`s

Rejected. Whether a token declares a binder would continue to depend on name
lookup, and static/nested argument syntax would remain a parallel type grammar.
Declaration syntax belongs in the prefix; the head is a nominal application.

### Parse the head as a general `TypeAnnotation`

Rejected after implementation experience. A general annotation admits sugar
(`[T]`, `T?`) and non-nominal shapes in head position, which then need either
post-parse rejection or provenance reconstruction (bracket sugar marks its
synthesized name span; optional sugar does not, so "what the user typed" is
not uniformly recoverable). It also routes heads through the formatter's
annotation sugar normalization, which rewrote core's `extend Array<Element>`
heads to `extend<Element> [Element]`. A dedicated `TypeApplication` node makes
the admission rule structural and keeps the formatter, elaborator, and tooling
preconditions in the type.

### Thread per-node conformance evidence through specializations

Rejected after implementation experience. Recording selected rows as evidence
lists on typed nodes and threading them through backend specializations —
merging call-site evidence with enclosing-instance evidence, canonicalizing
per module, deduplicating, and scanning by receiver and protocol — simulates
dictionary passing without the dictionaries being values in the program. Under
full-head coherence the deferred lookup is forced, so the threaded evidence
can never disagree with substitute-then-select and adds only machinery. If
evidence should ever become explicit, the right form is witness passing (the
checker elaborates dictionary parameters into the program); the shared catalog
selector and row identity built here are exactly what that elaboration would
consume, so this decision does not foreclose it.

### Treat `Self.Element == Int` only as a premise

Rejected. It would leave the head as `Array<T>`, make application depend on
predicate failure, and require contexts to establish disjointness. Canonical
head refinement makes it identical to `Array<Int>` before coherence or lookup.

### Add declaration-order or most-specific priority

Rejected by ADR 0016 and ADR 0035. This ADR adds concrete instance patterns, not
an ordered specialization relation.

### Keep separate matchers for typing and lowering

Rejected. It repeats semantic selection and permits frontend/backend
disagreement. Deferred monomorphization selection is legitimate, but it must use
the same catalog interface.

### Add arbitrary parameter-headed extensions

Rejected for this scope, consistent with ADR 0020. Nominal and protocol-head
instance schemes cover the intended uses without admitting unrestricted blanket
heads.
