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

`Parsed` holds source ASTs and parser diagnostics. `NameResolved` holds the
desugared, symbol-bearing ASTs and `ResolvedNames`. `Typed` holds one
`TypedProgram` and all parser, name-resolution, and type diagnostics accumulated
so far. There is no ownership-flow phase, lowering phase, IR, or execution phase.

`parse()` discovers reachable local imports. It scans explicit local imports and
qualified local references, queues their files, and continues until the complete
reachable source set has been parsed.

`resolve_names()` runs `src/desugar` before binding names. The resolver declares
and resolves symbols; it does not perform type or ownership analysis.

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

## Core and stdlib (`core.rs`, `stdlib.rs`)

Core and stdlib are ordinary Talk sources compiled lazily into module interfaces.
`TALK_CORE_PATH` and `TALK_STDLIB_PATH` can replace the bundled sources. A normal
`Driver::new` imports Core and the bundled stdlib interfaces; `Driver::new_bare`
skips that setup for core compilation and focused tests.

Only exported type information is retained. Backend body caches were deleted in
the frontend-only reset.

## Frontend consumers

- `src/analysis` and `src/lsp` provide diagnostics, hover, completion,
  definition, rename, formatting, and semantic tokens.
- `src/bin/talk.rs` exposes frontend CLI commands such as `check`, `parse`,
  `hover`, `format`, and package installation.
- `src/repl.rs` retains source-backed type queries and completion. Evaluation
  reports that execution is unavailable.
- `talk-c` and `wasm` preserve their embedding interfaces where practical;
  execution and backend-output calls return explicit frontend-only errors.
