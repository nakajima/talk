# ADR 0056: Cached library artifacts for local packages

Status: accepted; implemented (2026-08-10)

## Context

Package compiles fused every source into one unit: `talk test` in a
package re-parsed, re-resolved, and re-type-checked the package's own
library closure on every invocation, even when only test files had
changed. For a library of any size this dominated the edit-test loop
(a ~1k-line parser library added ~300 ms of frontend work to every
`talk test`, against a ~40 ms floor for a trivial package).

Locked dependencies already rode precompiled: each dependency library
compiles as its own module (absolute identity at mint, ADR 0038), its
typed bodies reach the backend through `DriverConfig::libraries`, and
its fact slice re-seeds the shared catalog on import (ADR 0053). But
dependency libraries were recompiled on every invocation too, and the
root package's own library never used the module boundary at all — its
sources always re-parsed into the binary or test compile.

## Decision

### 1. Package libraries cache like stdlib modules

A package library's compiled image — the `Module` interface (carrying
its ADR 0053 fact slice), the `TypedProgram` bodies, and the canonical
paths of its compile closure — is a pure function of its inputs and
caches under the shared artifact cache (src/compiling/cache.rs) at
`packages/<import-name>`. The key closes over:

- the manifest and every source under `src/` (a superset of the import
  closure: an unimported edit invalidates needlessly, a needed edit
  never stale-hits);
- the cache keys of the libraries it builds on (transitive by
  construction);
- its reserved session module id — symbols mint it, so a renumbered
  session (a lock change shifting reservations) must not read another
  session's image; and
- the compiler's content stamp, exactly as stdlib images.

This applies to locked dependencies (`compile_graph`) and to the root
package's own library target alike.

### 2. The root library's own compiles consume it through the module boundary

Binary (`talk run`) and test (`talk test`) compiles register the root
library as a finished module and bind `package::` imports of its
closure against the module's exports — the core redirect generalized.
`DriverConfig::precompiled_sources` maps the closure's canonical paths
to the module name; parse discovery leaves those files out of the
compile, and the name resolver binds single imports, globs wholly
inside the closure, and qualified references (`package::lib::f`)
against the module's export table.

Visibility outcomes are unchanged: file imports already admitted only
`pub` declarations, which is exactly the module export set. The REPL
consumes the root library through the same boundary and shares the
cache.

Two escapes keep the change semantics-preserving:

- **Fused fallback.** No library target, or a library that does not
  compile cleanly right now, produces no redirect: the compile proceeds
  fused, exactly as before, so a broken library's diagnostics render
  identically. (A broken library costs both compiles; only clean
  results are ever stored.)
- **`talk check` stays fused.** Workspace checking must diagnose the
  real sources, so it neither consumes the root library image nor
  redirects imports. Dependency libraries cache there too — that part
  changes no diagnostics.

### 3. Backend inputs close over library modules' stdlib edges

A library's typed bodies may call into stdlib modules the importing
program never names (a Markdown library using stdlib `html`; a
dependency using `dict`). The backend's body set previously closed over
registered *stdlib* modules' recorded edges only, so such calls failed
lowering ("no available source body"). The closure now seeds from every
registered module's CLEAN-03 dependency edges and follows unregistered
stdlib modules' own edges through the stdlib cache, making the body set
fully transitive.

## Consequences

- `talk test` after a test-only edit skips the library's whole frontend
  cost: the motivating package's runs dropped from ~520 ms to ~210 ms
  (release binary), with the remaining time in test compilation and the
  backend, which still compiles the reachable graph per run.
- Editing the library itself invalidates exactly its image (and nothing
  else); the run then costs what it always did, plus a small store.
- Packages with dependencies stop recompiling them per invocation.
- A library edit and a concurrent reader compute identical bytes;
  atomic rename keeps the cache race-free, and per-stem stamp retention
  bounds disk use.
- Two id spaces never meet: files inside the closure are never parsed
  by importing compiles, so no declaration exists both in the session's
  numbering and in the library's. A glob spanning the closure boundary
  keeps file semantics for its outside members; mixing such a glob with
  direct imports of the library in one file can observe both
  numberings. This is rejected by nobody and is a known, contrived
  limitation.
