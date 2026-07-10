# How the compilation pipeline fits together

This directory is the conductor: it owns the order of the stages the
other directories implement, the multi-file story, and the module/core
library plumbing. If you're tracing "what happens when I run `talk run
file.tlk`", start here.

## The driver (`driver.rs`)

`Driver` is a typestate pipeline — the compiler's phases are encoded
in the type, so consumers cannot call a stage out of order:

```
Driver<Initial>
  .parse()           -> Driver<Parsed>
  .resolve_names()   -> Driver<NameResolved> // desugars first
  .type_check()      -> Driver<Typed>        // TypedProgram + CheckedMir + flow facts
  .lower()           -> Driver<Lowered>      // lambda-G program
```

Each state carries that stage's outputs. `Parsed` holds parsed ASTs and
parser diagnostics. `NameResolved` holds the desugared, symbol-bearing
ASTs plus `ResolvedNames`. `Typed` holds a `TypedProgram`, the module's
`CheckedMir`, editor-facing `FlowFacts`, and all diagnostics so far.
`Lowered` holds the lambda-G `Program`, `main`, result type, the labels
that must become bytecode chunks, lowering diagnostics, and the earlier
compiler diagnostics.

The LSP/analysis path stops at `Typed` and keeps its own cloned
source-faithful ASTs for editor queries. `talk run`, `talk lower`,
`talk ir`, `talk build`, and the REPL go on to lowering and scheduling.

`parse()` also does **import discovery**. After parsing each file it
scans explicit local `use package::path` declarations and qualified references
such as `package::path::Name`, queues those files (adding `.tlk` when needed),
and keeps going until the reachable file closure is
parsed. Later stages therefore see the whole program, not one file at a
time.

`resolve_names()` runs the syntactic desugar pass (`src/desugar`) before
binding names. The resolver itself only declares and resolves symbols.

`type_check()` runs the constraint generator/solver (`src/types`), then
builds a `TypedProgram` for error-free source files and asks
`src/lower/mir.rs` for checked MIR. `mir::build_checked` owns the
structural body store, runs `src/flow`, and returns only the checked MIR
plus editor-facing flow facts.

`DriverConfig` controls the knobs: which module is being compiled (the
current program, core, or an external library), executable vs library
mode, the module name, the imported module environment, whether comments
are preserved (tooling wants them, compilation normally does not), and
strict vs lenient parsing. In strict mode a parse error aborts. In
lenient mode (what analysis/LSP use) the broken file contributes an
empty AST plus a diagnostic and the pipeline keeps going, so an editor
with a half-typed file still gets useful information for everything
else.

## Modules (`module.rs`)

`ModuleEnvironment` is the registry of compiled modules. A `Module`
carries its exported names (name -> symbol), display names for its
symbols, and its type payload (`ModuleTypes`: exported schemes plus the
module's slice of the type catalog). Its stable id is derived from its name
and exported surface. When a program imports a module, `import_as` retags the
module's symbols into the importer's module-id space; that is the point where
two compilations' id spaces touch.

## Packages (`package.rs`)

`package.rs` owns package manifests, lockfiles, source installation, and
package compilation. `stdlib/Package.tlk` defines the manifest schema and is
implicitly imported into `package.tlk` files only, so manifests use the normal
parser, resolver, and type checker. It resolves Git revisions to commits and
verifies tarball SHA-256 values before safely extracting tar or tar.gz source
into a content-addressed cache. The CLI uses the built-in Git/curl provider;
embedders can provide tar archives through `PackageSourceProvider` instead.
Local `.path` dependencies resolve relative to their declaring manifest and
remain at that location.
Each resolved package receives one module id for the whole graph. Its public
module interface and retained `LibraryTyped` body therefore use the same
cross-module symbols when the root binary or tests are lowered.

The root compiler environment receives only direct dependency interfaces;
transitive dependencies remain private to their declaring package. Lowering
receives typed library bodies for the complete graph, which is necessary for
whole-program specialization without making transitive package names
importable in source.

## The core library and stdlib (`core.rs`, `stdlib.rs`)

The core library is ordinary Talk source embedded into the binary (or
read from `TALK_CORE_PATH` when that override is set) and compiled once,
lazily, the first time a driver needs it. The stdlib follows the same
pattern with `TALK_STDLIB_PATH`. Current core files are:
`Ownership`, `Optional`, `Operators`, `Convert`, `String`, `Memory`,
`UnicodeData`, `Unicode`, `Array`, `Dict`, `Iterable`, `Async`, `IO`,
`Net`, `File`, `Showable`, `Http`, and `OS`.

Every `Driver::new` imports the compiled Core module into the module
environment, and each source file gets Core's exports as a prelude
unless that file starts with `// no-core`. `Driver::new_bare` skips that
setup and is used for compiling core itself and for deliberately small
tests.

`Driver::new` also imports the stdlib modules into the module
environment. The `fs`, `ansi`, `testing`, and `Package` modules are available
through package-style `use` imports rather than as a general prelude. `Package`
is additionally imported implicitly into files named `package.tlk`.

Core and stdlib keep typed artifacts beside their module exports:
`LibraryTyped` stores the `TypedProgram` and `CheckedMir`. Lowering needs
those bodies because generic functions, witness bodies, protocol defaults,
`@_ir` splices, derived operations, and other library code are specialized
on demand together with the using program.

## Everything around the pipeline

The thin layers that drive the driver live elsewhere but are worth
mapping here:

- `src/bin/talk.rs` — the CLI (`new`, `install`, `update`, `run`, `test`,
  `check` (`--json`), `parse`, `lower`, `ir`, `bytecode`, `build`,
  `run-bytecode`, `hover`,
  `format`, `html`, `repl`, `lsp`, `setup`, `completions`, `llm`, ...),
  each command a short wrapper over a driver or analysis workspace at the
  right stage. The printed `lower`/`ir` formats, plus source-level
  `@_ir`, are documented in `../../docs/ir-and-lambda-g-format.md`.
- `src/desugar/` — surface-syntax rewrites run between parsing and name
  resolution.
- `src/compiling/typed_program.rs` + `src/flow/` + `src/lower/mir.rs` —
  the typed program, checked MIR seam, and flow-sensitive ownership/drop
  analysis that lowering consumes.
- `src/cli/` — terminal concerns: diagnostic rendering with source
  excerpts and carets (colors off under `NO_COLOR`, JSON for
  `talk check --json`) and the interactive REPL frontend.
- `src/repl.rs` — REPL semantics, separate from its frontend: a session
  keeps previous declarations, recompiles the combined source on each new
  input, evaluates on the VM, and renders results in Talk syntax.
- `src/analysis/` + `src/lsp/` — the editor path; see the README in
  `src/lsp`.
- `src/common/` — the shared small stuff: the diagnostic envelope every
  stage's errors are wrapped in, id generation, and UTF-8/16 text-position
  math.
