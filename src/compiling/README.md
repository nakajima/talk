# How the compilation pipeline fits together

This directory is the conductor: it owns the order of the stages the
other directories implement, the multi-file story, and the core
library. If you're tracing "what happens when I run `talk run
file.tlk`", start here.

## The driver (`driver.rs`)

`Driver` is a typestate pipeline — the compiler's phases are encoded
in the type, so you physically can't call a stage out of order:

```
Driver<Initial>
  .parse()           -> Driver<Parsed>
  .resolve_names()   -> Driver<NameResolved>
  .type_check()      -> Driver<Typed>
  .lower()           -> Driver<Lowered>      // λ_G program
```

Each state carries that stage's outputs (ASTs, then resolved names,
then `TypeOutput`, then the λ_G `Program`), so a consumer like the
LSP can stop at `Typed` and never pay for lowering, while `talk run`
goes all the way and hands the program to the VM (or the reference
evaluator — both engines run the same lowered program).

`parse()` also does **import discovery**: after parsing a file it
extracts its `import … from ./path` statements, queues those files,
and keeps going until the closure is parsed — so the later stages
always see the whole program, never one file at a time.

`DriverConfig` controls the knobs: which module is being compiled
(the current program, the core library, or an external library),
executable vs library mode, whether comments are preserved (tooling
wants them, compilation doesn't), and strict vs lenient parsing. In
strict mode a parse error aborts; in lenient mode (what the LSP uses)
the broken file contributes an empty AST plus a diagnostic and the
pipeline keeps going, so an editor with a half-typed file still gets
hover and diagnostics for everything else.

## Modules (`module.rs`)

`ModuleEnvironment` is the registry of compiled modules. A `Module`
carries its exported names (name → symbol), display names for its
symbols, its type information (schemes + the type catalog), and a
stable id derived from hashing its exports — so a recompile that
doesn't change the surface keeps the same identity. When a program
imports a module, `import_as` remaps the module's symbols into the
importer's symbol space; that's the only point where two compilations'
id spaces touch.

## The core library (`core.rs`)

The standard library is ordinary Talk source — `Optional`,
`Operators`, `Convert`, `String`, `Memory`, `Array`, `Iterable`,
`Async`, `IO`, `Net`, `File`, `Showable`, `Http` — embedded into the
binary at build time from `core/*.tlk` and compiled once, lazily, the
first time a driver needs it. Every program implicitly imports it
(that's where `print`, `Optional`, operators, and the io surface come
from) unless the source starts with the `// no-core` marker, which the
small focused tests use to stay self-contained.

One subtlety: alongside the compiled module, core keeps its *typed
ASTs* around. Generic core functions can't be fully compiled ahead of
time — monomorphization needs the concrete types from the using
program — so the lowerer specializes core function bodies on demand,
straight from these retained ASTs, exactly as it does for the
program's own generics.

## Everything around the pipeline

The thin layers that drive the driver live elsewhere but are worth
mapping here:

- `src/bin/talk.rs` — the CLI (`run`, `check` (`--json`), `parse`,
  `lower` (the λ_G program), `ir` (the VM bytecode), `hover`,
  `format`, `repl`, `lsp`, …), each command a short wrapper over a
  driver at the right stage. The printed `lower`/`ir` formats, plus
  source-level `@_ir`, are documented in
  `../../docs/ir-and-lambda-g-format.md`.
- `src/cli/` — terminal concerns: diagnostic rendering with source
  excerpts and carets (`diagnostics.rs`, colors off under
  `NO_COLOR`), and the interactive REPL frontend (line editing,
  history, highlighting).
- `src/repl.rs` — REPL semantics, separate from its frontend: a
  session keeps the source of previous declarations and re-compiles
  them with each new line (so `let x = 1` persists), evaluates on the
  VM, and renders results in Talk syntax.
- `src/analysis/` + `src/lsp/` — the editor path; see the README in
  `src/lsp`.
- `src/common/` — the shared small stuff: the diagnostic envelope
  every stage's errors are wrapped in, id generation, and UTF-8/16
  text-position math.
