# 0026 - Hygienic, category-preserving syntax macros

Status: proposed

## Context

Talk needs a way to express source-level abstractions that ordinary functions
cannot provide: choosing syntax by arity or shape, introducing control flow,
recording source expressions, and deriving declarations from nominal types.
The compiler already has a suitable phase boundary: parsing produces a
source-spanned surface AST, then desugaring rewrites that AST before name
resolution assigns symbols.

A macro system must preserve properties that the rest of Talk relies on:

- lexical and sequential scoping, including module-level and local-function
  hoisting;
- source spans and `NodeID`s used by diagnostics and editor analysis;
- ordinary type, effect, ownership, and exhaustiveness checking of generated
  code;
- deterministic package builds and portable compiler embeddings; and
- the phase boundary in ADR 0035: static-value equality is decided by the
  restricted static expression language, not arbitrary compile-time execution.

Textual substitution is not suitable. It loses syntax categories and source
identity and permits accidental identifier capture. Unrestricted compiler
plugins or compile-time Talk evaluation would also make builds depend on host
code, ambient effects, and evaluator termination.

The relevant precedents point in a consistent direction:

- Scheme and Racket make hygiene and lexical context properties of syntax
  objects rather than naming conventions. Racket's set-of-scopes model handles
  generated definitions and recursive binding contexts.
- Rust `macro_rules!` demonstrates category-aware declarative matching with a
  fixed invocation grammar in a non-homoiconic language.
- Swift attached macros and OCaml extenders/derivers constrain what a
  transformer may add, improving composition and tooling.
- Lean demonstrates hygienic quotations, category-indexed syntax, and a
  restricted macro monad in a language with rich concrete syntax.
- MacroML, MetaML, MetaOCaml, Typed Template Haskell, and Scala show that typed
  staged code is valuable but carries materially different staging,
  polymorphism, and cross-stage-persistence concerns. It should not be the
  foundation of ordinary syntax macros.

## Decision

### Parsed, category-preserving expansion

Macros transform parsed syntax, not text. Public macro values are abstract
syntax objects indexed by category, conceptually `Syntax<Expr>`,
`Syntax<Pattern>`, `Syntax<Type>`, and `Syntax<Decl>`. They are not aliases for
the compiler's Rust AST structs.

Freestanding invocations use fixed, parser-known delimiters. The initial
expression spelling is:

```tlk
@name(argument, ...)
```

The `@` sigil distinguishes macro use, so macro names do not need a leading
underscore and do not compete with value names. Macros occupy a separate
namespace and exported macros follow ordinary package import selection and
aliasing.

Expansion runs after all reachable source files have parsed and before the
existing desugaring and name-resolution phases:

```text
parse -> collect macros -> expand -> desugar -> resolve names -> type check
```

Generated syntax is therefore subject to the same desugaring, binding, type,
effect, ownership, and lowering rules as source syntax. A generated local
`let` is sequential at its expansion position; a generated module declaration
participates in ordinary module predeclaration.

### Hygiene

Hygiene is mandatory, including for the first stable macro release.

- Syntax copied from an invocation retains its use-site lexical context.
- Identifiers written by a macro retain definition-site context.
- Bindings introduced by an expansion receive a fresh expansion scope, shared
  by their generated references but not by caller syntax.
- Macro-generated declarations can intentionally expose a caller-provided
  identifier by splicing that identifier as the binder.
- Constructing an identifier with call-site capture requires an explicit,
  visibly unsafe hygiene-bending operation. A raw string is never enough.

The implementation may use scope sets or an equivalent syntax-context model,
but alpha-renaming conventions such as `__macro_tmp` are not the language
contract.

### Declarative first, procedural later

The first authoring model is declarative token-template rules. A rule
captures its body as balanced tokens at definition and each invocation
position parses the substituted expansion against its own category, so one
definition form serves expression, block, and (later) declaration
positions. Arity is represented by distinct rules rather than inspecting an
untyped array of arguments.

A later procedural API may transform the same syntax objects. Procedural
transformers run as portable Talk macro bytecode in a restricted compile-time
environment, not as arbitrary native compiler plugins. Their effect row grants
only deterministic allocation and compiler-provided diagnostics by default.
Filesystem, environment, process, and network access require separate explicit,
build-tracked capabilities if they are ever admitted.

Procedural macros do not receive inferred types. A future typed-staging feature
may expose typed code values, but it is a separate decision and may not create a
solve-expand-solve inference cycle.

### Attached macros have roles

Attached macros are additive and declare a role such as member, peer,
extension, or conformance generation. A role bounds both the input context and
the declarations an expansion may emit. Where practical, an attached macro
also declares the names it can introduce so completion, collision checking,
and incremental compilation do not need to execute it speculatively.

Arbitrary whole-file AST rewriters are not part of the language.

### Expansion identity and diagnostics

Every template-generated node receives a fresh `NodeID`. Spliced source nodes
retain their source identity. The compiler retains both a source-faithful view
and an expanded compiler view, with an expansion map connecting invocations to
generated nodes.

Diagnostics produced while checking generated code blame the most relevant
source or template span and include a bounded expansion trace. Formatting
preserves macro definitions and invocations rather than printing expansions.
Rename, hover, and go-to-definition distinguish caller syntax,
template-introduced syntax, and definition-site references.

Expansion is deterministic and resource-bounded. Recursive expansion has a
fixed depth or work budget and reports the invocation chain when exceeded.

### Evaluation count

Hygiene does not make repeated splicing semantically harmless. Repeating an
expression can repeat effects, copies, borrows, or moves. Duplication is
permitted without ceremony: the first splice of a parameter retains the
source node's identity and later splices receive fresh identities, and
generated code remains the final authority — ordinary effect and ownership
checking must accept the expansion, so a duplicated move or borrow is
rejected the same way it would be if written by hand.

### Packages

A compiled module that exports macros carries a versioned macro interface in
addition to its ordinary type interface. Declarative rules are serialized as
syntax templates; procedural macros are serialized as portable macro bytecode.
Macro implementations are compile-time dependencies and do not become runtime
link dependencies merely because a consumer invokes them.

## First implementation slice

The first implementation intentionally proves only the expansion seam:

- file-local declarative macro declarations;
- one fixed-arity rule per declaration, with overloads selected by arity;
- `@name(...)` expression invocations;
- fresh node identities, recursive expansion limits, formatter/highlighter
  support, and structured diagnostics; and
- hygiene by construction: template-written names are stamped with the
  definition-site lexical scope plus a fresh expansion scope per expansion,
  so introduced binders neither capture caller names nor leak into caller
  scope, and template free names resolve at the definition site.

Declarative macros are category-agnostic token templates rather than parsed
expression rules. The body is captured as balanced tokens at definition;
each invocation position's grammar decides what the expansion must parse as.
There is one definition spelling:

```tlk
macro choose($condition, $yes, $no) { if $condition { $yes } else { $no } }

let value = @choose(flag, 1, 2)
```

A body that parses as one expression expands to that expression; anything
else expands to a block, so binders are ordinary template contents:

```tlk
macro once($value) { let y = $value
y + y }
```

Splice sites are validated at definition (an unknown `$name` is a
definition-time error); shape errors surface as ordinary parse, type, or
ownership errors at the invocation, blamed on the expansion.

Invocations are now implemented in every freestanding position. The same
`@name(argument, ...)` spelling is accepted in expression, item (root and
block), nominal-body, pattern, and type positions; each position parses the
substituted template against its own grammar category. Item and
nominal-body expansions splice their declarations where the invocation
stood, so a caller-provided `$name` in binder position is the intentional
way to expose a generated declaration, and nominal bodies parse with member
grammar so generated functions become methods. Multi-token arguments in
expression position are wrapped in synthetic grouping parentheses, so a
splice stays one syntax node; single-token arguments and declaration,
pattern, and type splices stay ungrouped. One consequence of the item
grammar: a bare `@name(...)` at statement level is an item-position
invocation, so its expansion splices statements and declarations rather
than evaluating as one expression.

The first slice also reserves one compiler-provided source-reflecting macro for
the test system:

```tlk
@assert(user.is_active())
```

It expands to one call of `testing::assert_message`, passing the condition once
and a message containing the condition's exact source bytes, for example
`"assertion failed: user.is_active()"`. The parsed driver retains its source
snapshot through expansion, so an edited file cannot make the message disagree
with the syntax that was compiled. This built-in is transitional evidence for
a future syntax-source operation and exported macro artifacts; it does not give
ordinary templates unrestricted source or compiler access.

Template hygiene now lands through the same set-of-scopes machinery the
procedural path uses (ADR 0043): every template-written name is stamped at
expansion, so binders, free identifiers, type names, and effect names are
all permitted in bodies without a capture-freedom caveat.

The first procedural follow-up is now implemented for expression macros. Sorted
`*.macro.tlk` units compile as a restricted Talk service; public functions
receive `MacroInput`, a use-site context, and a quotation context and return
`SyntaxResult<Expr>`. Freestanding invocations accept one arbitrary balanced
`()`, `[]`, or `{}` tree. Expression `quote { ... }` syntax captures canonical
tokens and supports named `$value` antiquotation without re-lexing. Expansion
uses fixed VM budgets, validates the already-parsed result and hygiene metadata
at the ABI boundary, and runs before desugaring and name resolution. Macro
units reject inline IR and `#unsafe`, and exported effects are limited to
deterministic allocation and the reserved diagnostic capability.

A library module serializes its macro service bytecode, ABI schema, and sorted
public macro export map beside its runtime interface. Ordinary package `use`
declarations import those macros into a separate compile-time namespace;
named imports, aliases, and import-all use the same spelling rules as runtime
symbols. Imported quotations carry a definition-module scope, so generated
identifiers resolve against the defining library's public runtime interface
rather than capturing names at the invocation site. Dependency compilation
loads and validates the service artifact instead of recompiling its macro
sources.

The bundled `html` stdlib module is the first production procedural macro.
It uses Maud-style syntax adapted to Talk expressions:

```tlk
use html::{ html, PreEscaped }

let names = ["Ada", "Grace"]
let title: String? = .some("People")
let page = @html {
    @let section = "people";
    main #(section) .page.featured[names.count > 0]
        title=[title] contenteditable[true] {
        @if let .some(heading) = title {
            h1 { (heading) }
        } @else if names.count == 0 {
            p { "Nobody is here." }
        }
        @for name in names { p { (name) } }
        @match title {
            .some(_) -> { small { "Named page" } },
            .none -> small { "Untitled page" }
        }
        (PreEscaped(value: "<hr>"))
    }
}
```

String literals and parenthesized interpolations are HTML-escaped. `Markup`
and `PreEscaped` render without a second escaping pass. Elements use braced
content, void elements end in `;`, and empty attributes may use either `name`
or legacy `name?`. Attributes support literal and parenthesized values,
braced concatenation, boolean toggles (`name[condition]`), and optional values
(`name=[optional]`). Class and ID shortcuts support static names, quoted names,
parenthesized values, and braced concatenation; classes may be toggled.
`@if`, `@else if`, `@if let`, `@for`, `@let`, and `@match` use Talk expressions
and patterns. `@for` accepts any Talk `Iterable`; the compiler completes
associated-type bindings from protocol equalities such as
`Iterator.Element == Iterable.Element`, preserving those bindings in exported
conformance rows so generic stdlib helpers specialize correctly downstream.

Attached roles, repetition, persistent expansion caching, and the complete
source/expanded analysis map remain follow-ups.

## Consequences

- The initial feature is less expressive than Rust procedural macros or Lisp
  macros, but generated code composes with Talk's existing semantic phases.
- Hygiene and source provenance are architectural inputs rather than cleanup
  work after a macro ecosystem exists.
- Fixed invocation syntax avoids making the hand-written parser, formatter,
  and editor grammar dynamically extensible.
- Type-aware generation, unrestricted compile-time evaluation, and static-value
  equality remain separate features.
- Module interfaces carry macro artifacts; incremental analysis still needs a
  persisted expansion-dependency and cache-key surface.

## Alternatives rejected

### Text or token substitution

Rejected because it cannot preserve binding, syntax categories, structured
source identity, or reliable tooling.

### Unhygienic AST rewriting with `gensym`

Rejected because accidental capture becomes a library convention instead of a
language invariant, and definition-site references remain vulnerable to
call-site shadowing.

### Native compiler plugins

Rejected because they are host-specific arbitrary code with weak
reproducibility and a poor fit for embedded and WebAssembly compiler surfaces.

### Type-aware macros as the only macro system

Rejected because declaration generation and Talk's inference groups would
create phase cycles, while most syntax abstraction does not need inferred type
information.

### Unrestricted compile-time Talk

Rejected because termination, ambient effects, and program equivalence would
leak into checking and type identity, contradicting ADR 0035's phase boundary.

### User-extensible grammar in the first release

Rejected because dynamic grammar affects parsing, formatting, recovery,
highlighting, and every editor client. Fixed delimited invocation sites cover
the initial use cases without that cost.

## References

- Kohlbecker et al., *Hygienic Macro Expansion* (1986).
- Clinger and Rees, *Macros That Work* (1991).
- Dybvig, Hieb, and Bruggeman, *Syntactic Abstraction in Scheme* (1993).
- Flatt, *Binding as Sets of Scopes* (POPL 2016).
- Ganz, Sabry, and Taha, *Macros as Multi-Stage Computations* (ICFP 2001).
- Ullrich and de Moura, *Beyond Notations: Hygienic Macro Expansion for
  Theorem Proving Languages* (IJCAR 2020).
- Racket Reference, *Syntax Model* and *Macros*.
- Rust Reference, *Macros by Example* and *Procedural Macros*.
- Swift Evolution SE-0389 and SE-0397.
- OCaml documentation, *Preprocessors and PPXs*.
