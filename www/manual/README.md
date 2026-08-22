# The TalkTalk Manual

TalkTalk is a programming language that looks a little like Swift or Rust. It checks your code before it runs, but tries to figure out most types for you.

This manual starts with small programs and works up to TalkTalk's more unusual features. The language is experimental and still changes quickly. Source files use `.tlk`, and the command-line tool is called `talk`.

## Start here

0. [Getting Started](getting-started.md)
1. [Syntax](syntax.md)
2. [Values and Types](values-and-types.md)
3. [Bindings and Functions](bindings-and-functions.md)
4. [Data and Patterns](data-and-patterns.md)
5. [Generics and Protocols](generics-and-protocols.md)
6. [Effects](effects.md)
7. [Ownership and Memory](ownership-and-memory.md)
8. [Collections and Text](collections-and-text.md)
9. [Modules and Packages](modules-and-packages.md)
10. [Macros](macros.md)
11. [Concurrency](concurrency.md)
12. [Testing](testing.md)
13. [The Standard Library](standard-library.md)
14. [The Toolchain](toolchain.md)
15. [Unsafe Code and Interop](unsafe-and-interop.md)

## Reference appendices

- [A. Type Inference Reference](type-inference.md)
- [B. MIR Reference](mir-reference.md)
- [C. Bytecode Reference](bytecode-reference.md)

## Reading the examples

TalkTalk source is fenced as `tlk`; terminal sessions are fenced as `sh`. On the website, an ordinary `tlk` block is editable and runnable. Each runnable block is a complete program unless the text says otherwise.

A block marked `norun` is displayed as source without interactive controls. It may describe an API boundary, depend on files not shown, or deliberately show only part of a program. A block marked `accumulate(name)` shares source with earlier blocks in the same named group. Running a later accumulated block also includes those earlier declarations.

Examples normally use the core library, which source files import automatically. A first line of `// no-core` disables that import for compiler and core-library work. Standard-library modules such as `task`, `fs`, and `dict` still require an explicit `use`.

Comments after expressions sometimes show expected output or explain a compile-time error. Placeholder text such as `...` is explanatory and is not valid TalkTalk unless the surrounding text explicitly defines it.

Shell commands that name repository paths assume the repository root. Commands without paths usually assume the current directory is inside a package. The manual calls out commands that behave differently outside a package.

The language changes quickly. The manual describes the supported source model; editor hover and public declarations in Core or the standard library show the exact current signatures. Compiler implementation documents under `docs/` explain design decisions but are not a second language specification.

The short command reference built into the compiler is also useful:

```sh
talk llm
```
