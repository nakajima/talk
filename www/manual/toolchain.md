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
talk repl --package
```

The package mode imports the current package library's public surface. The REPL supports declarations, type queries, completion, and indentation.

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

Use `--entry NAME` to choose a public zero-parameter function instead of the script's top-level statements.

## MIR and C

Inspect the optimized middle representation:

```sh
talk mir source.tlk
talk mir --no-opt --debug source.tlk
```

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

## Editor integration

```sh
talk lsp --stdio
talk setup nvim
talk completions zsh
```

The language server provides diagnostics, hover, completion, go-to-definition, rename, semantic tokens, and conservative code actions. `talk fix-labels` rewrites call sites when argument labels have changed:

```sh
talk fix-labels src/main.tlk
```

## Extending the command

Unknown commands use Git-style external subcommands. If `talk-report` is an executable on `PATH`, this invokes it with inherited standard streams:

```sh
talk report --format json
```

Built-in commands always take precedence.

## Compiler-development commands

`talk core-artifact` and `talk bootstrap` regenerate checked-in compiler artifacts. They are maintenance commands, not part of the application build loop. `talk llm` prints a compact, current language reference suitable for tools and agents.
