# Codebase cleanup and performance audit

Date: 2026-08-03  
Audited revision: `28b52743` (`main`), plus the working-tree state described under
Validation and scope.

## Executive summary

The compiler's major architectural seams are healthy. `talk-mir` is the right
target-neutral boundary, and `talk-native-runtime` already centralizes native
ABI and runtime generation. Those boundaries should be preserved.

The largest cleanup opportunities are in editor analysis, dependency tracking,
cache ownership, and Cargo feature boundaries:

1. LSP requests rediscover the workspace before they can hit the semantic
   cache, and edits invalidate every cached root.
2. Definition and rename independently implement position-to-symbol lookup and
   have already developed different behavior.
3. File and stdlib dependency graphs are reconstructed from strings in later
   phases instead of being recorded once by the Driver.
4. Editor rebuilds repeatedly clone source text, ASTs, and compiled modules.
5. Core and stdlib cache keys invalidate too broadly and are recomputed more
   often than necessary.
6. WASM and FFI builds compile unused or CLI-only dependencies.

The first five changes can reduce both code and latency. Runtime VM work is a
separate axis: the measured superinstructions should improve execution speed,
but will add a small amount of implementation code.

## Priority matrix

| Priority | Finding | Primary outcome | Estimated effort |
| --- | --- | --- | --- |
| P0 | CLEAN-01: LSP workspace inventory and invalidation | Editor latency | Medium to large |
| P0 | CLEAN-02: Shared semantic position resolver | Correctness and code reduction | Medium |
| P0 | CLEAN-03: Canonical dependency graph | Correctness and simpler compiler | Medium |
| P1 | CLEAN-04: Shared immutable sources and modules | Allocation and editor latency | Medium |
| P1 | CLEAN-05: Cache key and retention redesign | Cold-build performance | Medium |
| P1 | CLEAN-06: Shared requirement suggestion builder | Code reduction and consistency | Small |
| P1 | CLEAN-07: Cached text line index | Editor latency and code reduction | Small to medium |
| P1 | CLEAN-08: Cargo dependency and feature cleanup | Build time and artifact size | Small to medium |
| P1 | PERF-01: Profile-directed VM fusion | Runtime performance | Medium |
| P2 | CLEAN-09: Core and stdlib descriptor inventories | Maintainability | Small |
| P2 | CLEAN-10: Target-neutral backend facts | Prevent backend drift | Small to medium |
| P2 | CLEAN-11: Fixtures, generated files, and docs | Repository hygiene | Small |
| P2 | CLEAN-12: Lint policy and baseline | Build hygiene | Medium |

## Detailed findings

### CLEAN-01: LSP workspace inventory and invalidation

`workspace_analysis` cannot cheaply return a cached result. It first calls
`tlk_files_under_root`, walks the complete analysis root, and stats every Talk
file. Only after constructing the full version map does it compare that map
with the cached workspace.

Evidence:

- [`tlk_files_under_root`](../src/lsp/server.rs#L833) walks the root with
  `WalkBuilder`.
- [`workspace_analysis`](../src/lsp/server.rs#L883) builds the disk and open-file
  inventories before checking `state.workspaces`.
- [`file_stamp_version`](../src/lsp/server.rs#L759) truncates an mtime/length
  hash to an `i32`.
- Open, change, and close notifications call `state.workspaces.clear()` at
  [`server.rs`](../src/lsp/server.rs#L330), invalidating unrelated roots.

On a miss, [`AnalysisWorkspace::new`](../src/analysis/workspace.rs#L104):

- clones every source document;
- registers every stdlib module for editor auto-import support;
- parses, resolves, and type-checks the whole source set; and
- runs MIR ownership checking when frontend checking succeeds.

Recommended shape:

1. Maintain a per-root file inventory updated by LSP watched-file events.
2. Assign each root a generation and check it before any filesystem traversal.
3. Invalidate only the root containing the changed document.
4. Keep syntax and type diagnostics on the foreground path.
5. Run ownership analysis through a debounced, cancellable job whose result is
   associated with a specific workspace generation.
6. Move toward per-file parse caching and dependency-driven invalidation after
   CLEAN-03 establishes a canonical graph.

Expected result: cached hover, definition, rename, and completion requests no
longer perform a workspace walk, while unrelated roots retain their analysis.

### CLEAN-02: Shared semantic position resolver

Definition and rename independently traverse the AST to answer the same core
question: which semantic symbol is represented at a byte offset?

Definition's implementation starts in
[`definition.rs`](../src/analysis/definition.rs#L222). Rename's parallel
implementation includes
[`goto_definition_symbol_from_type_annotation`](../src/analysis/rename.rs#L377),
along with copies of path normalization, document lookup, member resolution,
effect-span handling, nominal-span handling, and identifier lookup.

The implementations have already drifted:

- Definition descends through nominal generic arguments, `Self`, tuples, and
  records in [`definition.rs`](../src/analysis/definition.rs#L308).
- Rename omits those variants and falls through to `_ => None` in
  [`rename.rs`](../src/analysis/rename.rs#L377).
- Rename resolves associated-type binding names and nominal-path members that
  definition does not handle equivalently.

Introduce one analysis-layer result containing:

- the resolved symbol;
- the source occurrence span; and
- an occurrence kind, such as declaration, reference, import alias, member, or
  associated-type binding.

Definition, rename, hover, and future refactors should consume that result.
Rename-specific collision detection and edit construction should remain in the
rename layer.

Before extraction, add characterization tests covering nested generic types,
tuple and record types, `Self`, associated bindings, nominal-path members,
effect names, and imports. The goal is to preserve the union of the two current
behaviors rather than selecting either implementation as authoritative.

### CLEAN-03: Canonical dependency graph

The Driver already discovers explicit imports and qualified local references
while parsing in [`extract_import_paths`](../src/compiling/driver.rs#L324). That
information is not preserved as the program's dependency graph.

Initialization ordering later reconstructs local edges by scanning typed root
declarations and matching the last import component to a file stem:
[`typed_program.rs`](../src/compiling/typed_program.rs#L65). This representation
can lose information when:

- different directories contain files with the same stem;
- a qualified local reference discovers a file without an explicit `use`; or
- `self`, `super`, and nested package paths need their canonical identity.

Stdlib dependencies are reconstructed separately by
[`dependencies_of`](../src/compiling/stdlib.rs#L199), which scrapes embedded
root-source lines beginning with `use package::`. Backend input closure consumes
those scraped edges in [`driver.rs`](../src/compiling/driver.rs#L851).

This is also inconsistent with `TALK_STDLIB_PATH`: compilation can read an
override directory while `dependencies_of` still reads `STDLIB_MODULES`'s
embedded text. The current working-tree implementation additionally uses this
scraper when importing dependencies during stdlib compilation.

Recommended shape:

1. During parse discovery, retain canonical `FileID -> FileID` local edges.
2. During module resolution, retain `ModuleId -> ModuleId` edges.
3. Store those edges in the parsed/resolved/typed program artifacts.
4. Make initialization ordering, stdlib compilation, backend body closure, and
   editor invalidation consume the stored graph.
5. Remove text scraping and file-stem reconstruction after callers migrate.

### CLEAN-04: Shared immutable sources and modules

An editor workspace currently creates several full copies of each document:

- `DocumentInput.text` already owns a `String`;
- `texts` clones it in [`workspace.rs`](../src/analysis/workspace.rs#L104);
- `Source::in_memory` clones it again;
- [`Source::read`](../src/compiling/driver.rs#L275) clones in-memory text;
- parsing clones the input into `source_texts` in
  [`driver.rs`](../src/compiling/driver.rs#L478).

The workspace also clones the resolved AST map before type checking, then
clones each AST again into its final file-indexed vector:
[`workspace.rs`](../src/analysis/workspace.rs#L185).

Module ownership has a similar mismatch. `ModuleEnvironment` stores
`Arc<Module>`, but [`import_compiled`](../src/compiling/module.rs#L229) accepts an
owned `Module` and wraps it in a fresh `Arc`. Callers deep-clone stdlib and
package modules that were already shared.

Recommended changes:

- Use a shared immutable source snapshot with `Arc<str>`.
- Attach CLEAN-07's line index to that snapshot.
- Let parsing and diagnostics retain the same text allocation.
- Move resolved ASTs when the phase transition permits it.
- Accept `Arc<Module>` in `import_compiled`; provide an owned convenience path
  only for freshly compiled modules.
- Store compiled package modules as `Arc<Module>`.
- Build a lightweight stdlib export index for auto-import and navigation, and
  merge full type catalogs only for imported modules.

### CLEAN-05: Cache key and retention redesign

The shared cache has several avoidable invalidation and ownership problems:

- The module documentation says key-stamped files let builds coexist, while
  [`store`](../src/compiling/cache.rs#L66) deletes every alternate key for the
  same stem.
- Core keys use executable mtime and length, so any relink invalidates frontend
  artifacts: [`core.rs`](../src/compiling/core.rs#L145).
- Every stdlib module hashes and allocates copies of the complete stdlib source
  set during load and again during cold-store:
  [`stdlib.rs`](../src/compiling/stdlib.rs#L294).
- A change to any stdlib source invalidates every stdlib module.
- [`cache::key`](../src/compiling/cache.rs#L33) concatenates paths and contents
  without length framing, so distinct input sequences can produce the same
  byte stream before hashing.
- The cache round-trip test uses the real user cache rather than an injected
  temporary directory.

Recommended changes:

1. Define an explicit serialization format version.
2. Generate a content identity for frontend-relevant compiler/schema code
   instead of using the final executable's mtime and length.
3. Length-prefix and domain-separate every hash input.
4. Memoize the bundled-source key. Keep override-directory keys dynamic.
5. Key each stdlib module on its own sources and actual transitive inputs.
6. Retain several stamped versions and apply bounded age, count, or size-based
   cleanup instead of deleting all siblings.
7. Inject the cache root so tests use isolated temporary directories.

### CLEAN-06: Shared requirement suggestion builder

Completion implements requirement source lookup, scheme fallback, implicit
`self` removal, and method stub construction in
[`completion.rs`](../src/analysis/completion.rs#L701).

Code actions repeat the same pipeline in
[`code_actions.rs`](../src/lsp/code_actions.rs#L2603). The two implementations
also use different semantic keys: completion primarily uses `Symbol`, while
code actions compare rendered protocol and requirement names.

Move this behavior into analysis as a symbol-keyed requirement suggestion that
contains the canonical signature and stub body. Completion and code actions
should only decide snippet syntax and edit placement. This removes compiler
semantics from the LSP transport adapter.

### CLEAN-07: Cached text line index

UTF-16 and line/column conversion is independently implemented in:

- [`common/text.rs`](../src/common/text.rs#L1);
- [`lsp/document.rs`](../src/lsp/document.rs#L51); and
- [`lsp/server.rs`](../src/lsp/server.rs#L1100).

Several conversions scan or count every newline before the requested offset.
Diagnostics repeat that work for both ends of every range.

Create one protocol-neutral line index containing byte offsets for line starts.
It should support byte-to-UTF-8, byte-to-UTF-16, UTF-16-to-byte, and range
conversion. Cache it on the shared source snapshot and update or replace it
when document text changes.

### CLEAN-08: Cargo dependency and feature cleanup

The root dependency list is in [`Cargo.toml`](../Cargo.toml#L21).

Dependencies with no Rust code usage found:

- `generational-arena`;
- `miette`;
- `futures`; and
- the root crate's direct `talk-native-runtime` dependency.

`talk-c` and `talk-llvm` should retain their own direct
`talk-native-runtime` dependencies.

`anyhow`, `tracing-subscriber`, and `tracing-tree` are used by CLI/LSP or tests
but are unconditional. As a result, `talk-ffi` and `talk-wasm` compile them even
though they depend on `talk` with `default-features = false`:
[`talk-ffi/Cargo.toml`](../talk-ffi/Cargo.toml#L10) and
[`wasm/Cargo.toml`](../wasm/Cargo.toml#L10).

Recommended manifest cleanup:

1. Remove the four unused direct dependencies.
2. Put `anyhow`, `tracing-subscriber`, and `tracing-tree` behind `cli`.
3. Make `talk-c` an optional native-C/bootstrap feature so WASM and FFI do not
   compile it when they do not expose C emission.
4. Remove `talk-mir` from `talk-llvm` dev-dependencies because it is already a
   normal dependency.
5. Explicitly list `talk-c` as a workspace member, or use a `talk-*` member
   glob. Cargo currently includes it only because it is an in-tree path
   dependency.
6. Remove or rename `.cargo/config.toml`'s `test` alias; Cargo reports that it
   is shadowed by the built-in command.
7. Resolve the `rustyline -> nix 0.31.3` future-incompatibility warning before
   the relevant Rust lint becomes a hard error.

After each feature change, compare `cargo tree -p talk-wasm` and
`cargo tree -p talk-ffi`, clean build time, and final WASM/static-library size.

### PERF-01: Profile-directed VM fusion

The repository already has sufficiently strong profiling data to rank the next
runtime work. [`profiling-findings.md`](profiling-findings.md#L20) records
175,259,482 executed frontend VM instructions and attributes 97.28% of the
critical path to the VM.

The measured next targets in
[`frontend-vm-report.md`](frontend-vm-report.md#L260) are:

1. 7,541,379 immediate `Cmp; Branch` pairs, 9.59% of dispatches.
2. 6,669,300 consecutive `GetField` edges, 8.48% of dispatches.
3. Broader inlining and calling-convention work. The remaining simple tail-call
   shape is only 0.51%.

Neither a semantic comparison-branch operation nor a field-path projection is
present today. [`CheckedIndexedLoad`](../talk-bytecode/src/checked_indexed_load.rs#L1)
is the appropriate precedent: recognize a proven MIR/bytecode shape, retain
validation and failure semantics, and replace its hot path with one operation.

Recommended order:

1. Implement a comparison-branch superinstruction only when the comparison
   result is otherwise dead.
2. Implement verified field-path projection that borrows through intermediate
   fields and materializes the final result with existing ownership semantics.
3. Reprofile before changing calls, returns, or frame layout.
4. Treat baseline native compilation as the longer-term ceiling, not as a
   substitute for the two already-measured VM wins.

### CLEAN-09: Core and stdlib descriptor inventories

Core filenames are independently maintained in `CORE_SOURCE_NAMES` and
`core_sources`: [`core.rs`](../src/compiling/core.rs#L40).

Stdlib facts are spread across `STDLIB_SOURCE_NAMES`, `STDLIB_MODULES`, and
`STDLIB_FILES`: [`stdlib.rs`](../src/compiling/stdlib.rs#L12).

Replace each family with one descriptor inventory from which names, embedded
sources, module IDs, and file lists are derived. Once CLEAN-03 lands, stdlib
dependency edges should also come from the compiler graph rather than being a
fourth hand-maintained field or text scraper.

### CLEAN-10: Target-neutral backend facts

C and LLVM necessarily have different syntax emitters, but they independently
compute some identical target-neutral properties. For example,
`needs_identity` is duplicated in
[`talk-c/src/lib.rs`](../talk-c/src/lib.rs#L1926) and
[`talk-llvm/src/emit.rs`](../talk-llvm/src/emit.rs#L1616). Symbol row ordering,
layout eligibility, and portions of display/type metadata preparation have
similar parallel structure.

Publish those facts from MIR or a small backend-planning layer. Do not attempt
to share target-specific string emission; that would obscure rather than
simplify each backend.

### CLEAN-11: Fixtures, generated files, and documentation

- Thirty-two of the thirty-three top-level `examples/*.tlk` files are
  byte-identical to `tests/examples/*.tlk`. Let the runtime corpus reference
  canonical example sources through a manifest while preserving the distinct
  expected-output contracts.
- Several reference-flow tests contain identical sources under different test
  names. Convert these to manifest-driven cases only where the runner category
  and expected disposition can remain explicit.
- `src/profile.rs` and `talk-vm/src/profile.rs` are exact nine-line copies. This
  is low priority and may not justify a new shared crate by itself.
- `rust-toolchain.toml` and `www/rust-toolchain.toml` are identical. Retain the
  nested copy only if `www` must build correctly when detached from this
  repository.
- `scripts/__pycache__/generate_daily_talk.cpython-313.pyc` is tracked. Delete
  it and ignore `__pycache__/` and `*.pyc`.
- [`src/compiling/README.md`](../src/compiling/README.md#L1) still says the
  repository is frontend-only and has no ownership, lowering, backend, or
  execution phase. It no longer describes the implementation.
- Profiling documents link to a deleted `profiles/frontend-vm` directory:
  [`profiling-findings.md`](profiling-findings.md#L6).
- `runs.txt` appears to be an informal historical timing log. Either document
  its generation and purpose or replace it with structured benchmark output.

The checked-in bootstrap C and TBC artifacts are not ordinary duplication:
native builds and WASM consume different forms, and the manifest verifies both.
Do not remove either without changing the bootstrap distribution design.

### CLEAN-12: Lint policy and baseline

The crate denies `unwrap`, `expect`, and `panic` in non-test builds:
[`lib.rs`](../src/lib.rs#L4). `cargo clippy --workspace --all-targets --locked`
currently reports 36 denied uses and 63 additional warnings in `talk`.

Many denied uses describe internal compiler invariants. Mechanically expanding
all of them into verbose control flow would increase code size without making
the compiler safer.

Adopt a deliberate split:

- user-triggerable failures return structured errors;
- verified internal invariants use narrowly scoped, documented lint allowances;
- stale patterns and ordinary warnings are fixed normally; and
- CI runs the agreed clippy command so the baseline cannot silently regress.

The existing unused `many` binding in
[`conformance.rs`](../src/types/solve/conformance.rs#L158) is an example of a
straightforward warning cleanup.

## Large-file assessment

The largest files include:

| File | Lines |
| --- | ---: |
| `src/compiling/mir/build/mod.rs` | 9,932 |
| `src/types/types_tests.rs` | 8,862 |
| `src/parsing/formatter.rs` | 3,944 |
| `talk-vm/src/interp.rs` | 3,808 |
| `src/lsp/server.rs` | 3,194 |
| `src/compiling/package.rs` | 2,864 |
| `src/lsp/code_actions.rs` | 2,791 |
| `talk-c/src/lib.rs` | 2,691 |

Large files are not automatically duplicated or slow. Split them only around
real ownership boundaries:

- MIR layout, release planning, verification, and expression/statement
  lowering are plausible separate modules.
- LSP request routing, workspace inventory, protocol conversions, and tests
  should not all live in `server.rs`.
- Package manifest, resolution, installation, graph compilation, and command
  orchestration can be separated.

These moves improve maintainability and review scope. They should not be
claimed as runtime or source-size wins unless they also eliminate duplicated
logic.

## Recommended implementation sequence

### Phase 1: Correctness-preserving consolidation

1. Add position-resolution characterization tests.
2. Implement CLEAN-02 and migrate definition and rename.
3. Add canonical dependency graph tests for qualified references, nested local
   paths, duplicate stems, stdlib overrides, and initialization order.
4. Implement CLEAN-03 and remove the reconstruction paths.
5. Implement CLEAN-06 and delete the duplicate signature/stub builders.

### Phase 2: Editor latency

1. Introduce the shared source snapshot and line index.
2. Change module imports to share `Arc<Module>`.
3. Add per-root LSP generations and root-specific invalidation.
4. Cache the file inventory through watched-file events.
5. Separate foreground frontend checking from debounced ownership checking.
6. Add or restore editor latency benchmarks covering cache hits, one-file
   edits, unopened-file changes, and multi-root workspaces.

### Phase 3: Build and artifact size

1. Remove unused dependencies.
2. Move CLI-only dependencies under the `cli` feature.
3. Gate native-C/bootstrap code for non-native consumers.
4. Redesign cache identities, module granularity, and retention.
5. Record clean build times and WASM/FFI artifact sizes before and after.

### Phase 4: Runtime performance

1. Implement comparison-branch fusion.
2. Re-run the existing VM instruction and native profiles.
3. Implement field-path projection if the profile still supports it.
4. Reprofile before broader call-frame or native-baseline work.

## Non-goals and cautions

- Do not merge the C and LLVM emitters wholesale. Share only target-neutral
  planning facts.
- Do not split large files solely to reduce line counts.
- Do not delete bootstrap artifacts as if they were accidental duplicates.
- Do not delete duplicate-looking tests without preserving runner category,
  diagnostics, and expected runtime output.
- Do not introduce a broad feature matrix without measuring whether each
  boundary actually removes dependencies or linked code.
- Do not treat the old profiling reports as permanent truth after changing the
  bytecode or interpreter; re-run them after each VM optimization.

## Validation and scope

The audit inspected the compiler pipeline, analysis/LSP layers, MIR and backend
adapters, VM profile reports, package/module machinery, cache implementation,
Cargo graph, examples and tests, generated artifacts, and architecture docs.

Validation performed:

- `cargo test --workspace --all-targets --locked` passed when the cache root was
  directed to a writable temporary directory.
- The initial cache round-trip failure under the restricted environment was
  caused by its attempt to write the user cache outside the writable workspace;
  the isolated test and complete suite passed with a temporary cache root.
- `cargo clippy --workspace --all-targets --locked` failed with the lint-policy
  baseline described in CLEAN-12.
- No implementation code was changed as part of the audit.

During the audit, unrelated or concurrent working-tree changes were present in
`Cargo.toml`, `src/compiling/stdlib.rs`, and `wasm/package.json`; an untracked
`examples/http_diag.rs` also appeared before this document was written. They
were preserved. Findings that reference the current stdlib dependency import
path account for the working-tree implementation visible during the audit.
