# 0041 - Callable argument labels and label-based overloading

Status: accepted; implemented (2026-07-25)

## Context

Talk parses argument labels but ordinary function calls do not give them
semantic meaning. A parameter such as `x` and an argument such as `x: value`
are currently connected only by position and type. The following calls
therefore behave alike even though their source communicates different APIs:

```talk
func id(x) {
    x
}

id(x: 123)
id(123)
id(other: 123)
```

This makes a written label decorative. It also prevents a function from
separating the name callers use from the local binder used by its body, and it
prevents labels from distinguishing overloads.

Enum variant payloads already have declaration-backed label checking, and
memberwise struct construction already exposes field labels to some editor
features. Ordinary functions, methods, explicit initializers, protocol
requirements, and effect operations have no equivalent callable contract.
The LSP can repair arity mismatches, but it cannot diagnose or repair a missing,
incorrect, or forbidden argument label.

Talk symbols are opaque identities. A `Symbol` distinguishes one declaration
from every other declaration, but scopes, member tables, protocol requirement
tables, and module exports are generally keyed only by a base source name.
Changing the binary shape of `Symbol` to contain labels would mix identity,
source lookup, and linkage while still leaving those name-keyed tables unable
to represent an overload set.

Trailing blocks are established call syntax in Talk. They are written outside
the parenthesized argument list and conventionally omit the final parameter's
label. Requiring every trailing-block API to declare `_` would make the
parameter declaration reflect a syntactic exception rather than the API's
normal labeled form.

## Decision

Named callables have source-level argument-label contracts. Labels are checked
in declaration order and participate in callable lookup. The local parameter
name does not participate in lookup.

### Parameter syntax

A parameter has an external argument label and a local binder name.

```talk
func same(x) { x }
func split(foo fizz) { fizz }
func positional(_ value) { value }
```

The declarations have these source-level callable names:

```text
same(x:)
split(foo:)
positional(_:)
```

The one-name form is shorthand for using the same spelling externally and
locally. The two-name form uses the first name as the external label and the
second as the local binder. `_` means that the argument must be unlabeled.

Ownership modes remain prefixes on the parameter and do not participate in the
callable name:

```talk
func store(consume value item: Item) { ... }
func update(mut _ item: Item) { ... }
```

Here the callable names are `store(value:)` and `update(_:)`; `item` is the
local binder in each body.

The implicit `self` parameter inserted for instance methods and initializers is
not part of the source-facing argument-label list. A protocol-static call form
that passes the receiver explicitly treats that receiver as a compiler-defined
unlabeled leading argument while retaining the requirement's declared labels
for the remaining arguments.

### Call-site rules

A normal argument must have exactly the label declared at its position.

```talk
func id(x) {
    x
}

id(x: 123)       // valid
id(123)          // missing label
id(other: 123)   // incorrect label
```

A parameter declared with `_` requires an unlabeled argument.

```talk
func id(_ x) {
    x
}

id(123)       // valid
id(x: 123)    // unexpected label
id(_: 123)    // unexpected label
```

`_:` is accepted by the parser as a written argument label so semantic
analysis can issue the argument-label diagnostic and the LSP can remove it. It
is never a valid call-site spelling.

Argument order remains declaration order. Labels do not permit argument
reordering. Label checking follows arity checking: a call with the wrong arity
reports the arity error and does not also report label mismatches for a partial
zip.

Call-site ownership markers belong to the argument value and follow the label:

```talk
sink.send(value: consume message)
counter.increment(by: mut amount)
```

Inserting, replacing, or removing a label must preserve the marker and value.

### Trailing blocks

One trailing block satisfies the final unfilled parameter regardless of that
parameter's external label. The label is omitted by the trailing-block syntax,
not by the declaration.

```talk
func map(transform fn: (Int) -> Int) { ... }

map(transform: { $0 }) // valid
map { $0 }             // also valid
```

The trailing block still participates in arity and type checking. Ordinary
parenthesized arguments preceding it must satisfy their labels normally. The
compiler preserves a trailing block as an explicit call-argument origin during
desugaring; semantic analysis does not infer this exception from a synthesized
function name or span.

Overload lookup ignores the final external label only for the argument supplied
by trailing-block syntax. If otherwise viable overloads differ only in that
final label, the trailing-block call is ambiguous. The caller can select one by
using the parenthesized, explicitly labeled closure form.

The LSP never offers an "add missing label" action for the trailing block.

### Named callables and function values

Argument labels belong to named callable interfaces, not to function types.
`Ty::Func` remains a type over parameter types, result, ownership modes encoded
in those types, and effects; it does not acquire source argument labels.

Converting a named function to a function value erases its labels, matching
Swift's distinction between declaration names and function types:

```talk
func id(value) {
    value
}

id(value: 123) // direct named call

let fn = id
fn(123)        // indirect function-value call
```

Calls through anonymous closures, function-typed parameters, stored function
fields, and other indirect function values are positional. A written label on
an indirect call is therefore unexpected. Anonymous closure parameters are
local binders only and do not define external labels.

Desugaring a named function declaration to a function-valued `let` must
preserve that it originated as a named callable. A general `let` whose value is
a closure does not gain a labeled callable interface merely because the binder
has a name.

### Callable names and symbols

A full callable name is a source-level declaration key:

```text
CallableName
  base: String
  labels: ordered list of Named(String) | Omitted
```

A callable contract associates that key and its callable role with an ordinary
`Symbol`. `Symbol` remains an opaque unique identity and retains its existing
serialization and runtime representation.

Only external labels participate in `CallableName`. Renaming the local `fizz`
in `func split(foo fizz)` does not change `split(foo:)`.

Callable contracts cover:

- module and local named functions;
- instance and static methods;
- explicit and synthesized memberwise initializers;
- protocol method and initializer requirements;
- conformance witnesses and protocol defaults; and
- effect operations.

Effect names remain non-overloadable, but their calls obey the same parameter
label rules. Enum variant payload labels keep their existing declaration
syntax and matching rules; this ADR does not reinterpret them as function
parameter labels.

### Label-based overloading

Scopes and callable member tables hold overload sets keyed by full
`CallableName`, not one callable symbol per base string.

```talk
func fizz(a: Int) { a }
func fizz(b: String) { b }
```

These declarations are `fizz(a:)` and `fizz(b:)` and may coexist. Their calls
select by labels before ordinary type checking:

```talk
fizz(a: 1)
fizz(b: "hello")
```

Two declarations with the same full callable name are duplicates. Parameter
types and local binder names do not distinguish declarations, so these remain
invalid overloads:

```talk
func fizz(_ a: Int) { a }
func fizz(_ b: String) { b } // duplicate fizz(_:)
```

This ADR does not introduce general type-directed overload resolution or
mode-only overloading. Labels are the only new overload discriminator.

A bare reference to a base name resolves directly only when the overload set
contains one callable. A larger set produces an ambiguous callable-reference
diagnostic. The first implementation does not add a special overload-reference
syntax; a caller can write a closure that invokes the desired labeled overload.

Methods, static methods, initializers, protocol requirements, protocol
witnesses, inherent extension members, and imported callables use the same full
name rule. Witness matching requires the witness's full callable name to agree
with the requirement's full name. Initializer selection uses its declared label
sequence instead of arity alone.

### Imports, exports, and linkage

Module interfaces preserve overload sets and callable contracts. Importing a
base name imports its callable overload set. Public declarations with the same
base but different full callable names must not overwrite one another in the
export table.

Stable module identity includes full exported callable names rather than only
base-name keys. Any external or public callable link name that must be unique is
derived from the full callable name, while runtime call instructions continue
to use the selected `Symbol`. Display names may show either the base name or the
full callable name according to context, but they are not lookup authority.

### Callable and call-resolution products

The checked frontend product carries serializable callable contracts keyed by
`Symbol`. Imported contracts merge alongside imported schemes and catalog
information.

Typing also publishes the selected callable symbol for every statically
resolved call site. This includes direct calls, methods, static members,
initializers, requirements, witnesses, and effects. Editor tooling and lowering
consume that selected resolution rather than searching a catalog again.

Compiler-generated operator, subscript, iteration, and other sugar calls are
not source label occurrences. Their lowering selects the compiler-defined
callable semantically and does not report source label-spelling errors. If a
sugar operation's callable target is not uniquely determined under its own
language rule, that is an ambiguity in the sugar contract, not permission to
choose an overload by table order.

## Diagnostics

Argument-label failures are structured diagnostics. A diagnostic carries:

- the selected callable when one is known;
- the expected and written label sequence;
- every mismatched argument position;
- the call and argument node identities needed for exact edits; and
- whether an argument originated as a trailing block.

The stable diagnostic code is `type.argument-label-mismatch` when the selected
callable is known during typing. Name or member lookup may report a distinct
structured no-matching-overload diagnostic when no callable can be selected.
Message wording is not an editor interface.

Representative messages are:

```text
Missing argument label 'x'
Expected argument label 'foo', found 'fizz'
Unexpected argument label 'x'
Unexpected argument label '_'
```

When no exact overload exists but one same-base, same-arity candidate remains,
resolution may recover to that candidate, report its label mismatch, and
continue type checking to avoid cascades. When several candidates remain,
analysis reports the candidate full names and does not guess. Type information
does not break the tie under this ADR.

## LSP code actions

The LSP matches the structured diagnostic and emits one atomic quick fix for a
selected callable's complete label mismatch.

| Source problem | Edit |
| --- | --- |
| `id(123)` expected `x:` | insert `x: ` before the argument marker or value |
| `id(fizz: 123)` expected `foo:` | replace only `fizz` with `foo` |
| `id(x: 123)` expected `_` | remove `x:` and following whitespace |
| `id(_: 123)` expected `_` | remove `_:` and following whitespace |

Deletion ends at the ownership marker when present, otherwise at the value
expression. Consequently `id(consume value)` becomes
`id(x: consume value)`, and removing a label from
`id(x: consume value)` preserves `consume value`.

A multi-argument mismatch is repaired with one workspace edit so applying the
action cannot leave an intermediate mixture of old and new labels. Actions are
offered only for a unique selected or uniquely recoverable candidate. An
ambiguous overload set receives no guessed label rewrite.

The existing arity action uses callable contracts for ordinary functions,
methods, requirements, effects, and explicit initializers when constructing
missing argument placeholders. A named expected slot inserts `label: {}`; an
omitted slot inserts `{}`. A trailing block is not diagnosed as missing its
final label and is not rewritten solely to add one.

All edit ranges are derived from parser spans and converted to UTF-16 only at
the LSP boundary, preserving ADR 0028's structured-diagnostic rule.

## Rename and definition behavior

External labels and local parameter binders are distinct semantic roles.
Ordinary parameter rename continues to rename the local binder and its body
references. When the declaration uses one-token shorthand, renaming the local
binder preserves the callable API by expanding the declaration:

```talk
func id(value) { value }
```

renamed locally from `value` to `item` becomes:

```talk
func id(value item) { item }
```

It does not silently rename every call from `value:` to `item:`. An external
API-label rename is a separate symbol-and-slot-aware operation and is not
required in the first implementation. Go-to-definition from a checked call
label may select the external-label token in the selected callable declaration.

## Implementation order

1. Add the external label and its span to `Parameter`, parse the one-name,
   two-name, and `_` forms, and parse `_:` as a written call label. Update the
   formatter, highlighter, AST constructors, and parser tests.
2. Preserve named-declaration versus anonymous-closure origin through function
   desugaring. Give desugared trailing blocks an explicit argument origin.
3. Introduce `ArgumentLabel`, `CallableName`, and the serializable callable
   contract. Register contracts for every named callable while excluding
   implicit receivers from source-facing labels.
4. Carry callable contracts through `TypeOutput`, module interfaces, catalog
   merging, imports, and exports. Publish one selected callable resolution per
   statically resolved call.
5. Enforce labels for the current single-candidate paths without changing
   `Ty::Func`: direct calls, indirect function values, methods, statics,
   initializers, requirements, and effects. Apply the trailing-block exception
   by argument origin.
6. Add the structured mismatch diagnostic and conservative LSP insert,
   replace, and remove actions. Generalize the arity action to callable
   contracts and protect local parameter rename shorthand.
7. Replace base-name callable maps with full-name overload sets in scopes,
   member catalogs, initializer tables, protocol requirement and witness
   tables, and module exports. Add exact-label selection, duplicate detection,
   unique recovery, and ambiguous-reference diagnostics.
8. Migrate core, stdlib, examples, benchmarks, tests, and generated fixtures.
   Add labels at calls by default; declare `_` only where the API is genuinely
   positional. Existing trailing-block APIs keep meaningful final labels and
   need no `_` migration solely for trailing syntax.
9. Remove compatibility paths that treated ordinary source labels as
   decorative and make the full validation suite the rollout gate.

These steps may land as separate green commits, but the data model is chosen
up front so label enforcement is not later retrofitted around overloads.

## Validation

Required coverage includes:

- parser and formatter round trips for `x`, `foo fizz`, `_ x`, and each
  ownership-mode combination;
- `_:` reaching semantic analysis rather than failing parsing;
- valid, missing, incorrect, and unexpected labels on direct functions;
- instance methods, static methods, explicit and memberwise initializers,
  protocol requirements, defaults, witnesses, and effect operations;
- label ordering and suppression of label cascades after arity failures;
- trailing blocks satisfying a named final parameter;
- ordinary preceding arguments retaining label enforcement when a trailing
  block is present;
- ambiguity when overloads differ only in the final label hidden by trailing
  syntax, and explicit parenthesized labels selecting either overload;
- label erasure through local aliases, callback parameters, stored function
  fields, and anonymous closures;
- exact selection of `fizz(a:)` and `fizz(b:)`, rejection of duplicate full
  names, and rejection of type-only overloads;
- ambiguous bare references to overload sets;
- full-name protocol witness matching and initializer selection;
- imported and exported overload sets surviving module serialization and
  preserving stable module identity;
- compiler-generated sugar selecting its semantic target without source label
  diagnostics;
- all four LSP edit forms, multiple edits in one action, ownership markers,
  multiline calls, nested expressions, and UTF-16 ranges after non-ASCII text;
- no missing-label action for a trailing block;
- arity placeholders using named and omitted callable slots; and
- local rename of a shorthand parameter preserving its external label.

The repository migration is complete only when the Rust test suite, Talk core
and stdlib tests, examples, and benchmark corpus all pass under mandatory
labels with no compatibility mode.

## Alternatives rejected

### Keep labels as documentation only

Rejected because misspelled and omitted labels continue to compile, source API
intent cannot be enforced, and labels cannot distinguish declarations.

### Put labels in `Ty::Func`

Rejected because labels are declaration names, not function-type behavior.
It would make callbacks and stored function values carry source API spelling,
prevent Swift-style label erasure, and force unification and every type
traversal to understand names that have no runtime meaning.

### Encode labels inside `Symbol`

Rejected because symbols already provide unique identity. Lookup tables,
exports, and protocol/member catalogs would still need overload-set keys, while
symbol serialization and runtime identity would become coupled to source
spelling. A `CallableName -> Symbol` association provides the needed separation.

### Permit type-directed overloads in the same change

Rejected. Selecting declarations by inferred argument types would introduce a
new constraint-solving and coherence problem. Full argument labels provide a
complete deterministic key for the overloads admitted by this ADR.

### Treat local parameter names as overload keys

Rejected because `func split(foo fizz)` deliberately separates the external
API from the body binder. Local refactoring must not change overload identity.

### Require `_` for every trailing-block parameter

Rejected. Trailing-block syntax intentionally omits the final label. Forcing
`_` into declarations would make APIs positional in every call form merely to
accommodate one syntactic form, and would prevent an explicitly parenthesized
call from using the meaningful label.

### Reorder arguments by label

Rejected. It changes evaluation order or requires another evaluation-order
rule. Labels validate ordered slots; they do not turn calls into unordered
records.

### Guess an LSP repair among overloads

Rejected. A quick fix may use a selected or uniquely recoverable callable but
must not choose an API based on declaration order or spelling distance when
several full names remain viable.

## Relationship to earlier decisions

This ADR extends ADR 0028's structured diagnostic and conservative code-action
policy. Label actions match semantic diagnostic payloads, preserve evaluated
argument expressions, and avoid guesses among overloads.

It follows ADR 0032's rule that checked call-argument labels and selected calls
are frontend semantic facts. The callable contract and per-call resolution are
the authority consumed by editor tooling and downstream phases; consumers do
not reconstruct a selected initializer, method, requirement, or function from
source text.

It preserves ADR 0018's ownership-marker placement. Labels are edited around
`borrow`, `mut`, `consume`, and `copy` markers without changing the selected
passing mode.

Enum variant payload labels retain their existing constructor-scheme metadata
and validation. They may share the low-level `ArgumentLabel` representation,
but their declaration grammar and variant-specific diagnostics are not
replaced by this ADR.

## Consequences

- Ordinary parameter names become enforced external API by default.
- APIs can use concise local binder names without sacrificing descriptive call
  sites.
- `_` is an explicit declaration of positional calling rather than an ignored
  spelling.
- Labels provide deterministic overload identity without type-directed
  overload resolution.
- Function values stay structurally typed and positional.
- Trailing blocks remain ergonomic while explicit parenthesized calls retain
  meaningful final labels.
- Public exports, imports, protocol witness tables, and initializer tables grow
  from single base-name entries to overload sets.
- The compiler and module interface gain callable-contract metadata, but the
  runtime representation of symbols and function calls does not gain labels.
- Parameter rename must preserve the external API when expanding shorthand.
- Existing Talk source requires a broad, intentional migration; positional
  declarations are chosen explicitly rather than inferred from legacy calls.
