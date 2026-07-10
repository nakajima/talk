# 0023 - Packages

Status: proposed

Date: 2026-07-09

## Context

Talk needs reusable units of source code that can be fetched from remote
sources, compiled as ordinary external modules, and used by another package.
V1 needs reproducible installs, but does not need a central registry or a
version solver.

The compiler already distinguishes package imports from relative file imports.
A package import resolves an external compiled `Module`; a relative import
resolves a source file in the current compilation. Packages should preserve
that boundary rather than flattening dependency source into the consumer's
source workspace.

## Decision

A directory containing a `package.tlk` manifest is a package. A manifest is
restricted declarative data: it is not evaluated as arbitrary Talk code. It
may contain only the literal fields and dependency/target forms defined by the
package manifest schema.

Packages are source packages. V1 installs remote Git repositories and remote
tarballs, or resolves local path dependencies, records the complete transitive
dependency graph in `package.lock`, and compiles every package as an external
module.
There is no package registry, package publication protocol, or semantic-version
constraint solver.

## Manifest

```tlk
Package(
    name: "talk-html",
    version: "0.1.0",
    builds: [
        .lib(from: "src/lib.tlk"),
        .bin(named: "talkhtml", from: "src/bin/talkhtml.tlk")
    ],
    dependencies: [
        .git(
            package: "talk-wasm",
            url: "https://github.com/nakajima/talk-wasm",
            rev: "v0.1.0"
        ),
        .tar(
            package: "talk-json",
            url: "https://example.com/talk-json-0.1.0.tar.gz",
            sha256: "..."
        ),
        .path(
            package: "talk-local",
            path: "../talk-local"
        )
    ]
)
```

Conceptually, the manifest data model is:

```tlk
enum PackageArtifact {
    case lib(from: String)
    case bin(named: String, from: String)
}

enum PackageDependency {
    case git(package: String, url: String, rev: String)
    case tar(package: String, url: String, sha256: String)
    case path(package: String, path: String)
}

struct Package {
    let name: String
    let version: String
    let builds: Array<PackageArtifact>
    let dependencies: Array<PackageDependency>
}
```

A package has at most one `.lib` target and any number of uniquely named
`.bin` targets. A library target is optional for a binary-only package. The
library's module identity is the package identity; it does not receive a
separate artifact name. Binaries are executable entry points and are never
importable packages.

`version` is release metadata in V1. It is recorded in the lockfile and used
for diagnostics, but no dependency form accepts a version range and no
resolver selects versions.

A dependency's `package` is its expected manifest name. Installation fails if
the fetched package's `Package.name` differs. This makes a URL/ref mistake
visible before compilation and avoids treating a URL as a package identity.

`rev` selects a Git revision and may name a commit, tag, or branch. Resolution
pins it to an exact commit in the lockfile. A tar dependency must specify its
SHA-256 in the manifest; the downloaded bytes must match before extraction.

A `.path` dependency is a local development dependency. Its path is relative
to the declaring `package.tlk`, must name a directory containing `package.tlk`,
and is never fetched or copied into the package cache. The lockfile retains
the relative path and its declaring package so a transitive path remains
relative to its own package. Path dependency source contents are intentionally
mutable; the lockfile records the dependency graph, not a content hash.

There is deliberately no `as:` field on dependencies.

## Package names and imports

A package's manifest name is its external identity and may use package-style
characters such as `-`. Its Talk import name is derived from that identity:

1. Preserve ASCII letters, ASCII digits, and `_`.
2. Replace every other character with `_`, one character at a time.
3. If the result cannot be lexed as a non-keyword Talk identifier, prefix it
   with `pkg_`.

For example, `talk-html` imports as `talk_html`:

```tlk
use { encode } from talk_wasm
```

The package identity remains `talk-wasm`; normalization only determines its
name in Talk source. It is not stored as an independent user-controlled alias.

Two direct dependencies of one package must not normalize to the same import
name. For example, `talk-html` and `talk_html` conflict. Installation must
fail with both original names and the colliding normalized name in the
diagnostic. It must not silently choose one, append a hash, or change an
import spelling. A dependency import name must also not collide with a
compiler-provided package module.

Transitive dependencies are resolved and compiled, but are not automatically
importable by a consumer. A package source file may import only its own direct
dependencies. Each dependency may, in turn, import its own direct
dependencies.

## Layout and source boundaries

```text
talk-html/
|- package.tlk
|- package.lock
|- src/
|  |- lib.tlk
|  `- bin/
|     `- talkhtml.tlk
`- tests/
   `- html.test.tlk
```

A target entry point and its reachable relative-import closure form that
target's local source workspace. Package source imports must remain within the
package's `src/` directory; dependency source is available only through a
package import.

A binary is compiled with its package library, when present, and its direct
dependencies in the module environment. It may import its package library
using the derived import name. Tests under `tests/` are compiled with the same
library and dependency environment. Test files follow the existing
`*.test.tlk` convention.

`buildin/` is not part of a package layout. Build outputs and installed
packages are not source files and must not be placed under the package source
tree.

## Resolution, installation, and the lockfile

`package.lock` is a checked-in, complete record of the resolved dependency
graph. For every package it records at least:

- manifest name and declared version;
- source kind and source URL or relative path;
- exact Git commit, tarball SHA-256, or path-dependency base; and
- resolved direct dependency edges.

The lockfile format is versioned. The source identity, rather than only the
manifest name, identifies a locked package, so different revisions of the
same named package can exist in different dependency subgraphs.

Installed remote package sources live in a content-addressed user cache.
Installing materializes verified Git and tarball sources into that cache; path
dependencies remain at their declared locations. Installation never copies
dependencies into the project or makes them globally importable. The cache is
an implementation detail, not a replacement for `package.lock`.

V1 uses the host `git` executable for Git sources and `curl` plus `tar` for
remote archives. A missing tool is an installation error. This avoids adding a
network or archive dependency to the compiler.

The CLI surface is:

```sh
talk new <name>
talk install
talk update [package ...]
talk build
talk run
talk test
```

- `talk new <name>` creates `<name>/` with a runnable `main` binary target
  and an example test.
- With no lockfile, `talk install` resolves the manifest graph, fetches and
  verifies its sources, and writes `package.lock`.
- With a valid lockfile, `talk install` uses only its exact locked sources and
  materializes any missing cache entries. It does not advance Git refs.
- `talk update` intentionally re-resolves the selected dependency refs, or all
  refs when no package is named, then rewrites the lockfile.
- `talk build`, `talk run`, and `talk test` require a lockfile whose direct
  dependency declarations match `package.tlk`. They use only its exact graph
  and may fetch a missing locked source into the cache.
- `--offline` prohibits network access for installation, building, running,
  and testing. A missing cache entry is then an error.

A changed manifest with a stale lockfile is an error. The user must run
`talk update` to accept a new resolved graph. Dependency cycles are detected
while resolving and reported as package dependency cycles.

## Compilation model

The package resolver first obtains and validates the locked source graph. The
compiler then processes packages in dependency order:

1. compile each dependency's library target as an external `Module`;
2. place that module in its dependent package's module environment under its
   derived import name;
3. compile the dependent library and then its binaries or tests.

Only public declarations from a library module are importable. This preserves
the existing module finalization and import/export boundary, including the
requirement that no unresolved type variables cross module boundaries.

## Non-goals

V1 does not include:

- a package registry, registry accounts, or publishing protocol;
- semantic-version ranges or version selection;
- dependency aliases or user-defined import names;
- multiple importable libraries in one package;
- vendoring dependencies into the package directory; or
- implicit access to transitive dependencies.

These can be designed later without changing the locked-source and external
module boundaries established here.

## Validation

The implementation is complete when tests cover:

1. Git resolution records an exact commit and a later locked install does not
   advance a branch or tag;
2. tarball checksum mismatches fail before extraction;
3. fetched manifest-name mismatches and normalized-import collisions fail
   clearly;
4. path dependencies resolve relative to both root and transitive package
   manifests without network or cache access;
5. offline installation succeeds from a populated cache and fails for a
   missing remote entry;
6. a package can import a direct dependency but not an undeclared transitive
   dependency; and
7. package library, binary, and test compilation preserve the behavior of the
   existing module compiler.
