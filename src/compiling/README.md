# How the frontend pipeline fits together

This directory owns the ordered frontend stages, multi-file import discovery,
and module/core/stdlib plumbing. The repository is intentionally frontend-only
while the execution backend is rebuilt.

## The driver (`driver.rs`)

`Driver` encodes frontend phases in its type:

```text
Driver<Initial>
  .parse()         -> Driver<Parsed>
  .resolve_names() -> Driver<NameResolved>
  .type_check()    -> Driver<Typed>
```

`Parsed` holds source ASTs, the exact source snapshot keyed by file id, and
parser diagnostics. The snapshot lets source-reflecting macros use the same
bytes that were parsed rather than re-reading a changing file. During
`resolve_names()`, the first ADR 0026 expression-template macros expand before
desugaring; macro declarations and invocation placeholders do not cross the
name-resolution seam. `NameResolved` holds the desugared, symbol-bearing ASTs
and `ResolvedNames`. `Typed` holds one
`TypedProgram` and all parser, name-resolution, and type diagnostics accumulated
so far. There is no ownership-flow phase, lowering phase, IR, or execution phase.

`parse()` discovers reachable local imports. It scans explicit local imports and
qualified local references, queues their files, and continues until the complete
reachable source set has been parsed.

`resolve_names()` runs `src/macro_expansion.rs` and then `src/desugar` before
binding names. The resolver declares and resolves symbols; it does not perform
type or ownership analysis.

`type_check()` runs the constraint generator and solver in `src/types`, then
builds a `TypedProgram` for source files without error diagnostics. The
`TypedProgram` is the final frontend artifact.

`DriverConfig` selects the module id, module environment, executable or library
type-checking mode, source roots, parser strictness, and comment preservation.
Lenient parsing lets editor analysis continue through incomplete files.

## Typed programs (`typed_program.rs`, `typed_program/build.rs`)

`TypedProgram` owns the checked semantic tree, resolved names, and `TypeOutput`.
The builder applies type-directed source elaborations once, including stored-field
projections, variant construction, explicit clone coercions, and `for` expansion.
No later compiler module currently consumes this artifact; it is the intended
starting seam for a future backend.

## Modules (`module.rs`)

A `Module` carries exported names, symbol display names, and `ModuleTypes`:
portable schemes plus the module's type-catalog slice. `ModuleEnvironment`
imports those interfaces into another frontend compilation. Module symbols are
retagged when imported so separately compiled symbol-id spaces remain distinct.

## Packages (`package.rs`)

Package support currently covers manifest parsing and type checking, lockfiles,
dependency resolution, source installation, Git revision resolution, SHA-256
verification, and safe tar extraction. Package binary compilation and Talk test
execution are absent with the backend.

## Builtin packages (`builtin_packages.rs`)

The bundled library (fs, testing, syntax, html, ...) is a set of ordinary
Talk packages under `packages/`. A bare `use name` activates one during
parse discovery, but it compiles and caches through the package library
pipeline: the manifest names the library target and dependencies, and the
compiled image replays from the shared disk cache. Each package registers
under a permanent `WellKnown` slot (absolute identity, ADR 0038); a retired
slot never returns. The `Package` package bootstraps the manifest DSL, so
it alone compiles manifest-free from its known library root.

## Core (`core.rs`)

Core is ordinary Talk source compiled lazily into a module interface plus
typed bodies. `TALK_CORE_PATH` can replace the bundled sources. A normal
`Driver::new` imports Core; `Driver::new_bare` skips that setup for core
compilation and focused tests.

## Frontend consumers

- `src/analysis` and `src/lsp` provide diagnostics, hover, completion,
  definition, rename, formatting, and semantic tokens.
- `src/bin/talk.rs` exposes frontend CLI commands such as `check`, `parse`,
  `hover`, `format`, and package installation.
- `src/repl.rs` retains source-backed type queries and completion. Evaluation
  reports that execution is unavailable.
- `talk-ffi` and `wasm` preserve their embedding interfaces where practical;
  execution and backend-output calls return explicit frontend-only errors.
