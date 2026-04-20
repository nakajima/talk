# A10: Repo hygiene and archaeology debt

**Severity:** Medium-low  
**Area:** repository clarity / contributor experience / operational cleanliness

## Summary

The repository contains a mix of current implementation, useful design notes, stale artifacts, historical code snapshots, disabled benchmarks, and miscellaneous scratch files. None of these items are catastrophic individually, but together they increase cognitive load and make it harder to tell what is authoritative.

## Evidence

Examples observed during audit:

- benchmark sources parked as text files:
  - `benches/compiler.rs.txt`
  - `benches/interpreter.rs.txt`
- benchmark targets commented out in `Cargo.toml`
- scratch or placeholder files such as:
  - `src/lsp/SLOP`
  - `wasm/SLOP`
- large historical/experimental material in `documents/`
- missing top-level `README.md` for the main project despite substantial scope
- assorted log and temp artifacts at repo root (`test.log`, `server.log`, `.tmp/*`, etc.)

## Why this matters

This creates a mild but real clarity tax:

- unclear starting point for new contributors
- uncertainty about which docs are current
- stale performance scaffolding
- more noise in root-level navigation
- harder codebase storytelling during reviews or audits

A compiler/runtime repo of this size benefits significantly from explicit signals about:

- what is production
- what is experimental
- what is historical reference material
- how to run the main workflows

## Recommended cleanup areas

## 1. Add a top-level README

At minimum it should explain:

- what Talk is
- how the compiler pipeline is organized
- how to run tests
- how to use the CLI
- how the wasm/www pieces fit in
- where active design docs live

## 2. Clarify documentation boundaries

Consider distinguishing:

- `docs/` for active documentation
- `documents/` or `archive/` for historical notes

If `documents/` remains, add an index stating what is current vs archival.

## 3. Decide the fate of bench scaffolding

Either:

- restore working benchmark sources and cargo bench integration, or
- remove stale bench remnants until they are ready to return

## 4. Remove or explain scratch markers

Files like `SLOP` may be useful as private reminders, but they create ambiguity in a shared repo. Either delete them or replace them with structured tracking in docs/issues.

## 5. Keep generated logs and temporary artifacts out of the repo surface

If they are needed locally, ensure they are ignored and not mistaken for maintained project files.

## Acceptance criteria

- The repository has an authoritative top-level README.
- Active docs and archival notes are clearly separated.
- Benchmark status is explicit.
- Root-level noise is reduced enough that the current system is easy to identify.

## Related issues

- [A05](./A05-interpreter-byte-conversion-overhead.md): performance work benefits from real, maintained benchmarks
- [A09](./A09-large-hotspot-files.md): maintainability work should be paired with better repo navigation and documentation
