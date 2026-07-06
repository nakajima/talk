# How name resolution works

This directory connects identifiers in the desugared AST to `Symbol`s —
stable, unique ids for the things names refer to. After this stage,
compiler phases do not compare declarations by string name: the checker,
flow checker, lowerer, and LSP all speak symbols. Surface rewrites happen
before this stage in `src/desugar`; this directory's job is declaration,
import handling, scope construction, and name binding.

## Symbols (`symbol.rs`)

A `Symbol` says both *what kind* of thing a name is and *which one*:
`Struct`, `Enum`, `TypeAlias`, `Protocol`, `Global`, `Property`,
`InstanceMethod`, `StaticMethod`, `Initializer`, `Variant`,
`AssociatedType`, `MethodRequirement`, `Effect`, `TypeParameter`, local
binders of several flavors, synthesized symbols, and so on.
Module-level symbols are keyed by `(module id, local id)` so the same
library imported into different programs keeps a consistent identity;
purely local symbols are local indices. Builtin types (`Int`, `Float`,
`Bool`, `Void`, `Never`, `RawPtr`, `Byte`, ...), plus a few compiler
builtins, have fixed well-known ids and are declared into every file's
root scope.

The kind-in-the-symbol design pays off downstream: the checker can tell
a variant from a method from a field by looking at the symbol, without
consulting a second table just to classify the name.

## Two passes: declare, then resolve

**Pass 1 — declare** (`decl_declarer.rs`). Before resolving uses,
declarations are entered into per-file scopes in rounds:

1. module-scope nominal types across all files, and module-scope values;
2. effects;
3. module-scope type aliases;
4. imports, now that target files have public declarations to import;
5. a full declaration walk for members, fields, inits, methods,
   associated types, parameters, pattern binders, local bindings, and
   nested scopes.

The rounds make top-level forward references work: by the time any
module-level use is resolved, all top-level names from that file and its
imports have been declared. Local `let` bindings are sequential: their
initializer resolves against the enclosing scope, and the new binders
become visible only after the declaration exits. Function declarations
and named function literals are hoisted at their block entry so local
recursive functions can call themselves.

**Pass 2 — resolve** (`name_resolver.rs`). The resolver walks every
expression, statement, pattern, declaration, and type annotation. Scopes
are a map from owning node to `Scope`, with separate namespaces for
values, types, and active effect handlers, plus a parent link. Lookup
walks parents to the file root. On success, a `Name::Raw("foo")` becomes
`Name::Resolved(symbol, "foo")` in place. On failure, an undefined-name
diagnostic is recorded and resolution continues so one typo does not
cascade through the whole file.

While walking, the resolver records the facts later stages need in
`ResolvedNames`:

- `scopes` for editor queries and scope-based completions;
- `symbol_names` and `symbols_to_node` for diagnostics, hover,
  go-to-definition, and rename;
- `child_types`, the nested type/associated-type map used by type
  annotations and catalog construction;
- `public_symbols`, which become module exports and importable file
  symbols;
- `mutated_symbols`, read by the type checker's value restriction and by
  lowering's assignment conversion.

Explicit closure capture lists are resolved here because they are just
names in source. Implicit closure-capture analysis is flow-sensitive and
lives in `src/flow`, not in the resolver. Binding-group dependency
analysis is also a type-checker concern (`src/types/generate/support.rs`).

## Imports and qualified names

File imports use Talk's `use` syntax:

```talk
use { name } from ./file.tlk
use { OldName: LocalName } from ./file.tlk
use ./file.tlk
```

A relative import resolves against the target file's public symbols. The
driver discovers and parses relative imports before name resolution; the
resolver checks that each named import exists and is public, applies
aliases, and inserts the imported symbol into the importing file's root
scope. A path-only `use` imports all public, non-builtin symbols from the
target. Package-style imports (`use { name } from package` or `use package`)
resolve against the `ModuleEnvironment` instead of a source file.

Qualified names such as `./file::Thing`, `../lib::Thing`, and
`Package::Thing` are resolved through the same public-symbol rules. Core
library names arrive as a prelude from the compiled Core module unless
the file opted out with `// no-core`; explicit imports from core source
paths are redirected back to that compiled Core module to avoid duplicate
type identities.
