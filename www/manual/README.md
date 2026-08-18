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

## Conventions

Code meant for TalkTalk is fenced as `tlk`; terminal sessions are fenced as `sh`. Examples usually rely on the core library, which normal source files import automatically. A first line of `// no-core` disables that import for compiler and core-library work.

The short command reference built into the compiler is also useful:

```sh
talk llm
```
