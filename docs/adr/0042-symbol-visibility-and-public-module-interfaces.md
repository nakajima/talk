# 0042 - Symbol visibility and public module interfaces

Status: accepted; implemented (2026-07-26)

## Context

Talk has a `public` modifier, file imports, qualified names, compiled modules,
nominal members, extensions, protocol conformances, editor queries, and named
program entries. These surfaces do not currently share one visibility rule.
This ADR renames that source modifier to `pub`; references to `public` in the
context describe the implementation being replaced.

At module scope, name resolution records public symbols in a global set and
uses that set when importing from another source file. Compiled modules derive
an export-name map from the same set. Other semantic products are broader:
every module-owned scheme and the complete type catalog cross the module seam.
Fields, methods, initializers, enum variants, extension members, and
conformances therefore remain available to an importer even when their source
declarations are not marked `public`.

Member syntax and Core source expose the ambiguity. Some public types rely on
unmarked members being callable outside their declaring file. Other public
types, including `HttpServer`, `Rawfile`, `TcpStream`, and `Range`, mark only a
selected set of methods `public` and leave representation fields and helper
methods unmarked. The implementation currently treats both groups as though
every member were public, so the selective modifiers communicate an API that
the compiler does not enforce.

The existing syntax admits `public` in positions where it has no effect. A
local `let`, an import, an ordinary statement, and even a repeated
`public public` prefix can parse. Public destructuring is context-dependent:
its binders are not available to another source file during import processing,
but they can appear in a finalized compiled module. Import insertion also
overwrites same-named bindings rather than diagnosing a conflict.

Editor behavior has another visibility model. Completion enumerates final
scope maps, so a sequential local may be suggested before its declaration and
the last shadowing binding may be suggested earlier in the block. Member
completion enumerates the complete catalog. Definition and rename resolve
imports without sharing the compiler's accessibility check.

The existing documentation describes a private declaration as internal to its
file. ADR 0013 separately establishes sequential local scope and module-scope
predeclaration. ADR 0023 says only public declarations from a package library
are importable. ADR 0028 requires structured diagnostics and conservative code
actions. ADR 0032 requires frontend semantic decisions to be published once
rather than reconstructed downstream. ADR 0036 gives extension and conformance
rows canonical identities. ADR 0041 makes full callable names, rather than
base-name strings, the keys for callable lookup and export.

Talk needs one visibility matrix and one owner for applying it across source
resolution, member lookup, module interfaces, tooling, and lowering.

## Decision

Visibility is a source accessibility rule attached to a declaration and its
owner. It is distinct from semantic reachability inside a compiled artifact.
A private witness or generated supplier may be required to implement a public
contract without becoming a source-visible exported name.

The default source visibility is **file-private**. `pub` makes an admitted
declaration accessible from other source files and from importing modules.
The legacy `public` spelling is removed rather than retained as an alias; using
it produces a migration diagnostic directing the author to `pub`. Talk does
not introduce package-only or module-only visibility in this ADR. Such a level
may be added later with explicit syntax; it is never inferred from an unmarked
declaration.

### 1. Member visibility

Members of a public nominal are not public merely because their owner is
public. Stored properties, instance methods, static methods, explicit
initializers, inherent extension members, nested nominal types, and nested type
aliases are file-private by default and require their own `pub` modifier to be
accessed outside their declaring file.

```talk
pub struct Account {
    let token: String

    pub let display_name: String

    init(token: String, display_name: String) {
        self.token = token
        self.display_name = display_name
    }

    pub func name() -> String {
        self.display_name
    }

    func authenticate(candidate: String) -> Bool {
        candidate == self.token
    }
}
```

Outside this file, `Account`, `display_name`, and `name` are accessible.
`token`, the explicit initializer, and `authenticate` are not. Property
visibility controls source lookup only; mutability, borrowing, ownership, and
stored layout remain separate rules.

A public member must have a publicly accessible owner. Marking a member public
inside a private nominal is rejected rather than accepted as an unreachable
export.

```talk
struct Hidden {
    pub func reveal() {} // rejected: public member has a private owner
}
```

A private member is accessible anywhere in its declaring file, including from
other declarations and extensions in that file. An extension in another file
does not gain privileged access merely because it extends the same nominal.

#### Synthesized memberwise initializers

A synthesized memberwise initializer inherits the nominal's visibility. A
public struct with no explicit initializer therefore remains constructible
outside its file, preserving the useful data-structure default:

```talk
pub struct Point {
    pub let x: Int
    pub let y: Int
}

let point = Point(x: 1, y: 2)
```

The synthesized initializer includes every stored property, including private
properties. Its parameter and result types are consequently part of the public
API closure. If an author needs hidden representation or construction policy,
they declare at least one explicit initializer, which suppresses synthesis;
only explicit initializers marked `pub` are externally callable.

```talk
pub struct Session {
    let token: SecretToken

    init(token: SecretToken) {
        self.token = token
    }

    pub static func open() -> Session {
        Session(token: make_token())
    }
}
```

`Session` has no public initializer even though the nominal is public.

#### Enum cases

Enum cases inherit the enum's visibility. A public closed enum has public
cases; a private enum has private cases. `pub case` is rejected as redundant
syntax.

This rule keeps construction, pattern matching, and exhaustiveness aligned. A
future resilient or non-exhaustive enum design may add hidden cases through a
separate explicit feature; ordinary private cases on a public closed enum are
not admitted.

Methods and nested types declared in an enum follow the ordinary explicit
member rule.

#### Protocol members

Associated types, method requirements, and initializer requirements inherit
the protocol's visibility. They define the protocol contract and cannot be
made less visible than the protocol. Writing `pub` on a requirement or
associated type is rejected as redundant.

A default implementation in a public protocol is reachable through its public
requirement. It does not independently become an inherent public member unless
it is also declared as one under the ordinary member rules.

#### Inherent extensions

An inherent extension has no visibility of its own. `pub extend` is not
admitted. Each inherent member follows the explicit member rule:

```talk
extend Account {
    pub func summary() -> String { self.name() }
    func debug_token() -> String { self.token }
}
```

`summary` is exported when its owner and signature satisfy the public API
closure. `debug_token` remains file-private. An inherent extension of an
imported public type may add a public member to the current module's interface;
that member remains owned and supplied by the extending module.

#### Conformance witnesses

A method written to satisfy a protocol requirement is a witness, not an
inherent source-visible member merely because its requirement is public. The
conformance row controls its external semantic reachability.

A conformance is part of the public module interface when:

1. its self type is publicly nameable by an importer;
2. its target protocol is public;
3. its canonical instance head, protocol arguments, and context satisfy the
   public API closure; and
4. the conformance declaration is at module scope.

Otherwise the conformance is file-private. No `pub` modifier is written on
`extend`; conformance visibility is derived from its semantic conclusion so
coherence cannot vary with an omitted modifier. Exported conformance rows may
reference private witness symbols as implementation suppliers. Those symbols
cross the implementation/linkage seam but do not become importable source
names or inherent members.

A declaration that is both a conformance and an inherent extension applies the
rules independently: the conformance may be public while unmarked inherent
members remain private.

### 2. Declaration visibility matrix

| Declaration | Default | `pub` admitted | Effective public rule |
| --- | --- | --- | --- |
| Top-level struct, enum, protocol | File-private | Yes | Modifier plus public API closure |
| Top-level type alias | File-private | Yes | Modifier plus public API closure |
| Top-level function or function signature | File-private | Yes | Modifier plus public API closure |
| Top-level `let` binder | File-private | Yes | Every binder in the pattern is exported |
| Top-level effect | File-private | Yes | Modifier plus public API closure |
| Macro rule | File-private | No in the current macro design | `pub macro` remains a structured unsupported-export diagnostic until an accepted macro-export design |
| Import | File-local binding | No | Imports never re-export implicitly |
| Local `let`, local function, parameter, pattern binder | Lexical | No | ADR 0013 scope only |
| Struct or enum stored property | File-private | Yes | Owner and property contract must be public |
| Struct or enum method/static method | File-private | Yes | Owner and callable contract must be public |
| Explicit initializer | File-private | Yes | Owner and callable contract must be public |
| Synthesized memberwise initializer | Inherits nominal | Not written | Public nominal plus public API closure |
| Enum case | Inherits enum | No | Public exactly when enum is public |
| Protocol requirement or associated type | Inherits protocol | No | Public exactly when protocol is public |
| Nested nominal or type alias | File-private | Yes | Every enclosing owner and nested declaration must be public |
| Inherent extension member | File-private | Yes on the member | Extended type and member contract must be public |
| Conformance row | Derived | No on `extend` | Publicly nameable head and public protocol/context |
| Generated helper or witness supplier | Not source-visible | No | May be interface-reachable without an exported name |
| Explicit named program entry | File-private unless marked | Yes on the function | `--entry` continues to require a public zero-parameter function |

A `pub` prefix on a statement, expression, import, local declaration,
protocol requirement, enum case, or extension is a syntax or declaration
legality error at that prefix. Repeating a visibility modifier is likewise an
error. The formatter never silently removes an ineffective modifier.

### 3. Public API closure

A declaration cannot expose a symbol that its consumer is forbidden to name or
whose contract is absent from the public module interface.

The public API closure begins at:

- exported top-level names;
- public members;
- inherited public enum cases and protocol requirements;
- public synthesized initializers;
- exported conformance conclusions; and
- generated symbols explicitly referenced by those public contracts.

The closure walks every source-facing contract component:

- parameter and result types;
- stored-property and enum-payload types;
- generic parameter kinds and defaults;
- generic bounds and `where` predicates;
- effect operations and effect rows;
- nested type ownership;
- associated-type bindings;
- conformance heads, targets, and contexts; and
- callable names and overload contracts from ADR 0041.

Builtins and compiler-defined public Core symbols satisfy the closure. A
file-private source declaration does not. Function and method bodies may use
private declarations freely because implementation dependencies are not
source-facing contracts.

A closure violation is diagnosed at the public declaration and identifies the
private dependency and the contract position that exposes it.

```talk
struct Secret {}

pub func reveal() -> Secret { // rejected
    Secret()
}
```

The compiler does not repair a leak by silently exporting `Secret`, erasing the
type, or retaining an unnameable foreign symbol in the public interface.

### 4. Imports, qualification, and re-exports

A local source import and an external compiled-module import apply the same
rule: only exported names are importable. Named imports of private symbols
report an inaccessible-symbol diagnostic. Import-all skips private symbols.
Qualified lookup uses the same exported-name table and accessibility check.

An import creates a file-local binding. It does not copy the imported
symbol's exported status onto the binding and does not add an alias to the
current module's exports.

```talk
use package::peer::{ Original as LocalName }
```

`LocalName` is available only in the importing file. This ADR does not add
re-export syntax. `pub use` is rejected; a future ADR may introduce explicit
re-exports without changing ordinary import behavior.

Import insertion never overwrites an existing declaration or import. A
same-namespace collision is a structured diagnostic naming both sources.
Declaration order and hash-map order never choose the winner. Import-all also
diagnoses collisions rather than silently dropping or replacing one side.

All binders of a public top-level destructuring declaration are predeclared and
exported consistently. Local source imports and compiled-module imports
therefore observe the same export set.

### 5. Namespaces and visibility

Visibility filters an already well-defined declaration key; it is not an
overload or ambiguity resolver. A private declaration never permits a public
same-named declaration to overwrite it silently.

Ordinary module-level types and values share one source/export namespace. This
matches constructor use, import spelling, and the single qualified-name form.
Callable overloads within that namespace use ADR 0041's full callable names.
An unresolved bare callable reference follows ADR 0041's overload rules rather
than visibility-based selection.

Effect operations occupy the effect namespace selected by tick-prefixed effect
syntax. A value binding with the same text does not shadow an effect operation.

Nominal type members, including associated types, nested types, type aliases,
and nominal parameter projections from ADR 0036, occupy the nominal
type-member namespace. Value members occupy the nominal value-member namespace.
Both are owner-qualified and both carry visibility metadata.

Local values use ADR 0013's lexical namespace and source-position rules.

### 6. Source position and shadowing

This ADR does not change ADR 0013:

- module declarations are predeclared and order-independent;
- a local `let` becomes visible after its initializer;
- later local bindings shadow from their declaration point onward;
- local named functions are hoisted at block entry; and
- parameters, match binders, and block scopes retain their established rules.

Every compiler and editor query for visible symbols uses those same
source-position rules. A final scope snapshot is not sufficient for completion
because it cannot represent sequential visibility or the binding selected
before a later shadow.

### 7. Public module interfaces

A compiled module distinguishes three related products:

1. **exported names**, which source imports and qualified lookup may use;
2. **public semantic contracts**, the transitive API closure needed to type
   those names, members, cases, requirements, and conformances; and
3. **private implementation payload**, including bodies, private types,
   private helpers, generated glue, and private witness suppliers needed by
   compilation or linking.

Only the first product creates source-visible names. The second may include an
unnamed witness or generated supplier referenced by a public contract, but it
does not include unrelated private schemes or catalog rows. The third stays in
the owning compiled artifact and is not merged into an importing type-checker's
lookup catalog.

Module construction validates the public semantic closure before publication.
Importing a module merges only that validated interface into source typing.
Backend and linker artifacts may retain the private implementation payload
under their own verified contracts.

Stable module identity includes the complete exported declaration keys and
their public contracts. It is not derived from base-name strings alone.

### 8. Tooling

Completion, hover, definition, references, rename, semantic highlighting, and
code actions consume the same accessibility and source-position facts as the
compiler.

- Scope completion excludes declarations not yet visible at the cursor.
- Member completion excludes inaccessible members.
- Auto-import actions enumerate the target module's exported names, not raw
  root-scope maps.
- Definition and rename do not treat an invalid private import as a valid
  exported binding.
- Rename preserves visibility and does not create an import collision.
- Tooling may navigate a private symbol from an occurrence that is legally in
  its declaring file.

No editor module reconstructs visibility from source spelling, catalog
presence, or membership in an unowned global set.

## Diagnostics

Visibility failures are structured diagnostics with stable identity and
source ownership. Required categories include:

- visibility modifier not admitted on this declaration;
- repeated visibility modifier;
- public member with a private owner;
- inaccessible top-level symbol;
- inaccessible member;
- public API exposes a private declaration;
- import collision;
- duplicate exported declaration key; and
- malformed or incomplete public module interface.

Local-source and compiled-module imports use the same public-facing diagnostic
categories. Diagnostics need not reveal the existence of a private declaration
inside an external binary-only module when its interface intentionally omits
that information; they may report that the name is not exported. Source
workspaces may identify the declaration as private when its source is already
available to the compiler.

Diagnostics carry the declaration, access site, owner, and relevant contract
position needed by ADR 0028 tooling. Message wording is not the interface.

## Implementation sequence

1. Rename the source modifier from `public` to `pub`, update lexing, parsing,
   formatting, highlighting, diagnostics, and source-reflecting tooling, and
   emit a focused migration diagnostic for the removed spelling. Encode the
   matrix as declaration-legality checks in parsing or early semantic
   validation. Reject ineffective and repeated `pub` modifiers.
2. Record each declared symbol's defining file, owner, declaration role,
   declared visibility, and effective visibility in one resolver-owned
   semantic product.
3. Replace direct scope-map insertion with checked declaration/import
   insertion. Enforce namespace keys, duplicate declarations, import
   collisions, and complete public-pattern predeclaration.
4. Make source lookup and qualified lookup use one accessibility operation.
   Preserve ADR 0013 source-position facts for later editor queries.
5. Add visibility and ownership to nominal member, nested-type, inherent-row,
   and conformance catalog entries. Enforce member accessibility during type
   elaboration and member solving.
6. Implement public API closure validation and split module exported names,
   public semantic contracts, and private implementation payload.
7. Merge only validated public interfaces into importing type checkers. Keep
   private witness and generated supplier linkage explicit without making them
   source exports.
8. Route completion, auto-import, definition, references, rename, hover, and
   code actions through the resolver/catalog visibility operations.
9. Audit Core, stdlib, examples, tests, and benchmarks. Replace the legacy
   spelling and add `pub` to intended fields, methods, explicit initializers,
   nested types, and inherent extension members; leave representation and
   helpers private. Do not blanket-mark every current member public.
10. Remove the global boolean `public_symbols` policy and compatibility paths
    that infer member visibility from a public owner or catalog presence.

The migration may land in green stages, but no stage may silently narrow an
existing public API or retain two visibility authorities. Until Core migration
and module-interface validation land together, member enforcement remains
behind the branch implementing this ADR rather than a partial production rule.

## Validation

The implementation is complete when tests cover the full matrix through public
compiler interfaces.

### Members

- Private and public fields, methods, static methods, explicit initializers,
  nested types, and aliases on a public nominal.
- Access from the declaring file, a sibling source file, and an external
  compiled module.
- A public member rejected on a private owner.
- A public synthesized memberwise initializer and suppression by an explicit
  private initializer.
- Public API closure over synthesized initializer parameter types.
- Enum cases and protocol requirements inheriting owner visibility.
- Inherent extension members requiring explicit `pub`.
- A public conformance with private witness suppliers but no accidental
  inherent member export.

### Declarations and imports

- Every matrix row accepts or rejects `pub` as specified.
- `pub` on expressions, statements, imports, locals, cases, requirements,
  and extensions is rejected at the modifier.
- Legacy `public` receives the focused migration diagnostic and is never
  accepted as an alias for `pub`.
- Public destructuring exports every binder identically through local-source
  and compiled-module imports.
- Named, aliased, import-all, and qualified access share export rules.
- Local declarations, two named imports, and import-all collisions diagnose
  deterministically.
- Imports and aliases never become re-exports.

### Public interfaces

- Public signatures, fields, variants, bounds, effects, aliases, nested types,
  and conformances reject private source-facing dependencies.
- Private body-only dependencies remain valid.
- Importer catalogs contain the validated public closure but omit unrelated
  private schemes, members, aliases, rows, and conformances.
- Exported conformances retain exact canonical heads and private supplier
  linkage without exposing supplier names.
- Stable module identity changes when a public declaration key or contract
  changes.

### Scope and tooling

- Sequential completion before and after a local declaration and before and
  after a shadow agrees with compiler lookup.
- Member completion, hover, definition, rename, and auto-import agree with
  member and export accessibility.
- UTF-16 editor ranges remain correct for visibility diagnostics and actions.
- Explicit named entry selection accepts only a public zero-parameter
  function.

The Core migration gate includes source compilation, Core and stdlib tests,
examples, package/module boundary tests, editor tests, and every supported
execution engine.

## Consequences

### Benefits

- A public type has an auditable API rather than an automatically exposed
  implementation.
- Selective member modifiers in Core acquire the meaning their source already
  communicates.
- File imports and compiled modules expose the same declarations.
- Private source declarations stop leaking through complete imported catalogs.
- Conformance coherence remains semantic while witness implementation names
  remain private.
- Import collisions and namespace conflicts become deterministic diagnostics.
- Compiler and editor visibility gain locality behind one semantic policy.
- Future visibility levels or explicit re-exports can extend the matrix without
  changing member lookup and module construction independently.

### Costs

- Core and stdlib require a deliberate API audit. Many currently unmarked
  members are relied on externally and must be marked public; others will
  become genuinely private.
- Catalog and module serialization must carry visibility, ownership, and the
  validated public semantic closure.
- Member lookup needs the access-site file in addition to receiver type and
  label.
- Tooling can no longer answer visibility from final raw scope maps alone.
- Existing code that relied on accidental access to a private member or
  transitive imported catalog row will fail and require an intentional API.
- Public structs with synthesized memberwise initializers expose every
  initializer parameter type unless they declare explicit construction.

## Alternatives rejected

### Public nominal makes every member public

Rejected. It makes member-level `pub` decorative, exposes representation and
helpers, and contradicts the selective API style already present in Core.

### Public nominal makes every method public but fields private

Rejected. It still prevents helper methods from being private and gives
initializers, static methods, nested types, and extension members no coherent
rule.

### Infer public members from cross-file use

Rejected. Visibility would depend on the current program rather than the
owning declaration, and removing a consumer could silently change a compiled
module interface.

### Keep complete catalogs as imported interfaces

Rejected. Catalog presence becomes de facto accessibility, private types leak
through inference and member lookup, and importing an unrelated dependency can
change available conformances or methods.

### Make conformances explicitly `pub`

Rejected. A conformance conclusion participates in coherence and protocol
semantics as one unit. Deriving interface visibility from the public
nameability of its complete conclusion prevents a private witness modifier from
changing coherence and avoids treating witness methods as ordinary exports.

### Permit private cases in a public closed enum

Rejected. External construction and exhaustive matching would disagree about
the enum's actual inhabitants. Hidden cases require a separate resilience or
non-exhaustive-enum design.

### Treat imports as implicit re-exports

Rejected. A file-local convenience import should not enlarge a package API.
Re-exports require explicit syntax and their own collision and provenance
rules.

### Preserve silent import overwrite for convenience

Rejected. Declaration or hash-map order is not a semantic priority rule.
Silent overwrite can change symbol identity and corrupt nominal catalog entries.

### Let tooling approximate visibility

Rejected by ADR 0028 and ADR 0032. Approximation suggests invalid code, hides
valid code under sequential shadowing, and recreates policy outside its owning
module.

## Relationship to earlier decisions

This ADR preserves ADR 0013's sequential local scope and module-scope
predeclaration while requiring source-position queries to use those facts.

It completes ADR 0023's package rule that only public library declarations are
importable by defining public members, conformances, and the semantic closure
of an exported module interface.

It follows ADR 0028 by requiring structured visibility diagnostics and by
forbidding tooling from inferring fixes from messages or raw maps.

It follows ADR 0032 by making resolved visibility and validated module
interfaces frontend facts consumed by typing, tooling, lowering, and linking.

It uses ADR 0036's canonical instance heads when deriving conformance-interface
visibility and does not add declaration-order priority or a second row
identity.

It composes with ADR 0041: visibility applies to each full callable declaration
key and its overload set. Import/export tables must preserve distinct public
callable names without allowing a private overload or base-name collision to
be selected by map order.
