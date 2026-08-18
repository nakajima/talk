# 13. The Standard Library

Some useful types and functions are available in every TalkTalk file. Others live in modules that you import when you need them. This chapter shows what is available today; the standard library is still small and changes along with the language.

## Core, always in scope

Core provides:

- `String`, `Substring`, `Character`, Unicode and text operations
- `Array<T>`, `InlineArray<T, N>`, ranges, iterators, and adapters
- `Optional<T>` and `Result<S, F>`
- arithmetic, comparison, bitwise, conversion, and display protocols
- `Duration`, `Instant`, memory roles, effects, and resumptions
- `print`, `unreachable`, and host-boundary primitives

The first line `// no-core` disables this import for trusted low-level work.

## Files and paths

The `fs` module provides `Path`, `Directory`, `DirectoryEntry`, and `File`:

```tlk
use fs::{ File, Path }

let path = Path("notes.txt")
match File.open(path: path, mode: .r) {
    .ok(file) -> {
        match file.read() {
            .ok(contents) -> print(contents),
            .error(_) -> print("read failed")
        }
        file.close()
        ()
    },
    .error(_) -> print("open failed")
}
```

`Path.normalized()` performs lexical dot-component cleanup. `Path.expanded()` expands `~`, prepends the working directory, and normalizes. `Path.canonicalized()` asks the host to resolve an existing path and symlinks. Directory enumeration returns typed file, directory, or symlink entries.

`File` reports operation-specific errors through `Result`. Call `close()` when you are finished with an open file.

## Operating-system access

The `os` module exports the `OS` namespace:

```tlk
use os::{ OS }

print(OS.cwd())
print(OS.getenv(name: "HOME"))
print(OS.argc())
```

`OS.argc()` returns the process argument array despite its historical name. The first element identifies the invoked program; arguments after `talk run --` follow it.

## Networking and HTTP

`net` provides `TcpStream` and `TcpListener` over the host I/O effect. `http` provides `Request`, `Response`, route handlers, and `HttpServer`. These modules are currently compact foundations rather than a broad production web stack.

```tlk norun
use net::{ TcpListener }
```

See `examples/ChatServer.tlk`, `examples/ChatClient.tlk`, and `examples/Http.tlk` for complete current programs.

## Tasks and scheduling

`task` provides:

- `parallel_run` and `run_blocking`
- `Sender<T>`, `Receiver<T>`, and `channel<T>()`
- bounded channels
- `sleep`
- `select_recv`

Core automatically runs every executable under a cooperative root scheduler. The `coop` module provides `run` for an explicit nested scheduler scope. See [Concurrency](concurrency.md).

## Dictionaries

`dict` provides a growable string-keyed `Dict<Value>` with insertion and optional lookup. It is explicit rather than part of core:

```tlk norun
use dict::{ Dict }
```

## HTML and syntax

The `html` package contains the procedural `@html` macro and its HTML value type. The `syntax` modules expose typed lexer, parser, AST, documentation, and dump facilities used by self-hosted tools and procedural macro services.

## Testing

The `testing` module supplies the test prelude's registration and assertion effects. Normal `.test.tlk` files receive that prelude automatically; they do not need to import it.

## Reading the exact API

Until generated API pages exist, use source and editor hovers:

```sh
talk hover stdlib/fs.tlk --line 294 --column 12
talk check your-package/
```

Public declarations are marked `pub`, and the LSP exposes inferred signatures and documentation at use sites.
