# 14. The Toolchain

The `talk` command checks and runs programs, manages packages, runs tests, talks to editors, and builds files you can inspect or ship.

## The everyday loop

```sh
talk check
talk run
talk test
```

Inside a package these commands discover the enclosing manifest. With explicit files, they compile those sources as a program. `talk check --json` and `talk test --json` provide structured output.

Format a file to standard output:

```sh
talk format source.tlk
talk format --width 100 source.tlk
```

## The REPL and queries

Start the interactive frontend:

```sh
talk repl
```

Inside a package, the REPL imports the current package library's public surface automatically. Outside a package it starts a standalone session; use `talk repl --standalone` to ignore an enclosing package explicitly. The REPL supports declarations, type queries, completion, and indentation.

Query source directly with:

```sh
talk hover source.tlk --line 10 --column 5
talk parse source.tlk
talk html source.tlk
```

`hover` also accepts a byte offset or compiler node ID. `parse` and `html` are primarily compiler-development views.

## Bytecode

The default compiler target is a validated register-bytecode image:

```sh
talk build source.tlk -o program.tbc
talk run-image program.tbc
talk bytecode source.tlk
```

Use `--entry NAME` to choose a public zero-parameter function instead of the script's top-level statements. `talk bytecode` prints disassembly; `.tbc` is the encoded and validated transport format. See the [Bytecode Reference](bytecode-reference.md) for the image layout, instruction families, validation rules, and version policy.

## MIR and C

Inspect the optimized middle representation:

```sh
talk mir source.tlk
talk mir --no-opt --debug source.tlk
```

`--no-opt` shows MIR before optimization. `--debug` annotates instructions with source spans, binding names, and reasons for compiler-generated operations. The dump is an inspection format, not a stable serialization. See the [MIR Reference](mir-reference.md) for its control flow, layouts, instructions, cleanup, and target contract.

Emit C or build a native executable:

```sh
talk c source.tlk > program.c
talk build --native source.tlk -o program
talk build --native --keep-c source.tlk -o program
```

The native path uses `$CC`, then `cc`, unless `--cc` selects another compiler. `--target TRIPLE` cross-compiles through `zig cc`; `--cflag` passes an extra compiler argument.

## Packages

```sh
talk new NAME
talk install
talk dependencies
talk update [PACKAGE...]
```

See [Modules and Packages](modules-and-packages.md) for manifest and lockfile semantics.

## Editor integration and automatic repairs

```sh
talk lsp --stdio
talk setup nvim
talk completions zsh
```

The language server provides diagnostics, hover, completion, go-to-definition, rename, semantic tokens, and conservative code actions. `talk fixit` applies the same preferred, compiler-proven quick fixes without an editor:

```sh
talk fixit src/main.tlk
```

When no path is supplied inside a package, it repairs the package workspace. Ambiguous actions are never chosen automatically. Edits are rechecked between rounds so a repair can reveal another deterministic fix without applying overlapping stale edits.

## Extending the command

Unknown commands use Git-style external subcommands. If `talk-report` is an executable on `PATH`, this invokes it with inherited standard streams:

```sh
talk report --format json
```

Built-in commands always take precedence.

## Compiler-development commands

`talk core-artifact` and `talk bootstrap` regenerate checked-in compiler artifacts. They are maintenance commands, not part of the application build loop; the wasm build script runs `talk core-artifact` itself before embedding the artifact. `talk llm` prints a compact, current language reference suitable for tools and agents.
