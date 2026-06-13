# How name resolution works

This directory connects every identifier in the AST to a `Symbol` — a
stable, unique id for the thing the name refers to. After this stage,
nothing in the compiler compares names as strings: the checker, the
lowerer, and the LSP all speak symbols. A handful of desugaring
transforms also run here, before resolution, so later stages see a
smaller language than the parser accepts.

## Symbols (`symbol.rs`)

A `Symbol` says both *what kind* of thing a name is and *which one*:
`Struct`, `Enum`, `Protocol`, `Global`, `InstanceMethod`,
`Initializer`, `Variant`, `Property`, `Effect`, `TypeParameter`,
locals of several flavors, and so on. Module-level symbols are keyed
(module id, index) so the same library compiled into different
programs keeps consistent identities; purely local symbols are just
indices. Builtin types (`Int`, `Float`, `Bool`, `Void`, `Never`,
`RawPtr`, `Byte`, …) have fixed well-known ids, declared into every
file's root scope by `builtins.rs`.

The kind-in-the-symbol design pays off downstream: the checker can
tell a variant from a method from a field by looking at the symbol,
without consulting any other table.

## The desugaring transforms (`transforms/`)

Run on the freshly parsed AST, rewriting sugar into kernel forms:

- `lower_for_loops` — `for x in xs { … }` becomes a plain loop over
  `xs.iter()`, calling `.next()` and matching `some`/`none`.
- `lower_operators` — unary and binary operators become protocol
  method calls (`a + b` → `Add.add(a, b)`-shaped protocol-static
  dispatch); `&&`/`||` become `if` expressions so they
  short-circuit.
- `lower_funcs_to_lets` — a top-level `func f(…) { … }` becomes
  `let f = func f(…) { … }`, so the rest of the pipeline has exactly
  one kind of top-level value binding.
- `prepend_self_to_methods` — instance methods and protocol
  requirements get `self` as an explicit first parameter, so a method
  is just a function whose first argument is the receiver.

This is why the type checker has no operator rules and the lowerer
has no method-receiver special case: by the time they run, those
constructs no longer exist.

## Two passes: declare, then resolve

**Pass 1 — declare** (`decl_declarer.rs`). Before resolving anything,
declarations are entered into scopes in rounds: first the nominal
types (structs, enums, protocols), then effects, then top-level
values, then imports, then a full walk declaring everything else
(fields, methods, parameters, pattern bindings). The rounds are what
make top-level forward references work: by the time any *use* is
looked at, every top-level name in the file (and everything imported)
is already declared. Inside a function body, locals are declared as
the walk reaches them, so a local must be bound before it's used.

**Pass 2 — resolve** (`name_resolver.rs`). Walk every expression and
type annotation, looking names up through the scope chain. Scopes are
a map from owning node to `Scope` (separate namespaces for values,
types, and effect handlers), each with a parent link; lookup walks
parents to the file root. On success, the AST's `Name::Raw` becomes
`Name::Resolved(symbol, text)` in place. On failure, an
undefined-name diagnostic — resolution continues, so one typo
produces one error, not a cascade.

While walking, the resolver also records things later stages want:

- which symbols are **public** (exported, importable elsewhere);
- which symbols are ever **assigned to** (the checker's value
  restriction and the lowerer's cell allocation both read this);
- which outer bindings each function **captures** (closure
  conversion);
- a **dependency graph** between top-level bindings (`scc_graph.rs`
  computes its strongly connected components — note the type checker
  builds its own grouping over a slightly different edge set in
  `src/types/generate.rs`; see the README there).

All of it lands in `ResolvedNames`, the stage's output, consumed by
the checker, the lowerer, and the LSP (go to definition is "find the
symbol under the cursor, then find where it was declared"; rename is
"find every node resolving to this symbol").

## Imports

`import { name } from ./file.tlk` resolves against the target file's
public symbols. The driver (see `src/compiling`) discovers and parses
imported files; the resolver checks that each imported name actually
exists and is public in the target, then maps it into the importing
file's root scope. Core library names arrive the same way, just from
a prebuilt module instead of a file on disk.
