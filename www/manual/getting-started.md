# 0. Getting Started

This chapter gets a TalkTalk program running. We will build the compiler, run one file, and then create a small project. For now, building from the repository is the dependable way to install it.

## Build the compiler

TalkTalk's compiler is written in Rust and currently uses a pinned nightly Rust toolchain. From the repository root:

```sh
cargo build --release
./target/release/talk --version
```

Put `target/release/talk` somewhere on your `PATH` if you want to invoke it as `talk`. Released builds are also attached to the project's GitHub releases.

## Run one file

Create `hello.tlk`:

```tlk
print("Hello, TalkTalk!")
```

Then run it:

```sh
talk run hello.tlk
```

A source file may contain declarations and top-level statements. The value of the final top-level expression is printed when it is not `Void`:

```tlk
func square(_ n: Int) -> Int {
    n * n
}

square(6)
```

This prints `36`.

Use `talk check` when you only want diagnostics:

```sh
talk check hello.tlk
```

Both commands accept `-` as standard input where a source filename is accepted.

## Create a package

```sh
talk new hello
cd hello
talk run
talk test
```

The generated package contains:

```text
hello/
  package.tlk
  package.lock
  src/main.tlk
  tests/hello.test.tlk
```

`package.tlk` declares the package's build products and dependencies. `package.lock` records the resolved dependency graph and should be checked in. Inside a package, `talk run` chooses the package binary and `talk check` checks the package targets and tests.

Arguments after `--` are passed to the program:

```sh
talk run -- one two three
```

They are available through `OS.argc()` from the `os` standard-library module.

## Editor support

The compiler includes an LSP server and plain Neovim runtime files:

```sh
talk setup nvim
talk lsp --stdio
talk completions fish
```

`talk completions` also supports Bash, Elvish, PowerShell, and Zsh. The repository includes a VS Code extension under `dev/editors/vscode`.

## Where to next

Read [Syntax](syntax.md) and [Values and Types](values-and-types.md) for the language's basic shape. [Data and Patterns](data-and-patterns.md), [Generics and Protocols](generics-and-protocols.md), and [Effects](effects.md) cover the features that most distinguish TalkTalk.
