# 9. Modules and Packages

As a program grows, you can split it across files and bring names in with `use`. A package groups those files into a library or executable and records any outside code the project needs.

## Visibility

Top-level declarations and members are private to their file unless marked `pub`:

```tlk norun
pub struct User {
    pub let name: String
}

pub func load_user() -> User {
    User(name: "Ada")
}
```

Only a module's public surface can be imported elsewhere.

## Imports

`use` can select names, alias them, import a module surface, or recursively import source submodules:

```tlk norun
use package::models::{ User, load as load_user }
use package::models
use package::models::*
use self::child::{ value }
use super::shared::{ Thing }
use dependency::{ API }
```

Paths have distinct roots:

- `package::` begins at the current package's source root
- `self::` begins beside the importing module
- `super::` begins at its parent module
- a dependency name begins at an external package's exported surface

`use path` imports that module's public surface. `use path::*` additionally walks source submodules recursively.

## The core and standard libraries

Normal files implicitly receive the core library: primitives, arrays, strings, optional and result types, operators, iteration, `Showable`, memory roles, and host effects. A first line of `// no-core` disables it.

Modules under `stdlib/` are explicit imports, such as:

```tlk norun
use fs::{ File, Path }
use os::{ OS }
use task::{ channel, sleep }
```

## Package manifests

`talk new hello` creates a `package.tlk` like this:

```tlk norun
Package(
    name: "hello",
    version: "0.1.0",
    builds: [.bin(named: "main", from: "src/main.tlk")],
    dependencies: []
)
```

A package may build libraries and named binaries:

```tlk norun
let builds: [PackageArtifact] = [
    .lib(from: "src/lib.tlk"),
    .bin(named: "server", from: "src/server.tlk")
]
```

Run a named binary with:

```sh
talk run --bin server
```

## Dependencies and the lockfile

Dependencies may come from Git, a verified tar archive, or a local path:

```tlk norun
let dependencies: [PackageDependency] = [
    .git(package: "widgets", url: "https://example.test/widgets.git", rev: "abc123"),
    .tar(package: "codec", url: "https://example.test/codec.tar.gz", sha256: "..."),
    .path(package: "shared", path: "../shared")
]
```

Use the package commands to manage resolution:

```sh
talk install
talk dependencies
talk update
talk update widgets
```

`talk install` resolves the graph into `package.lock`. `talk update` refreshes all or selected dependencies. `--offline` requires all needed sources to be available locally.

## Package-aware commands

From anywhere inside a package, `talk run`, `talk check`, `talk test`, and the LSP locate the enclosing manifest. `talk check` with no filenames checks the package's declared targets and tests rather than every stray `.tlk` file under the directory.
