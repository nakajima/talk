# A04: LSP full-workspace rebuild behavior

**Severity:** High for editor responsiveness  
**Area:** LSP / analysis pipeline / incremental performance  
**Primary files:** `src/lsp/server.rs`, `src/analysis/workspace.rs`

## Summary

The LSP currently invalidates cached analysis very coarsely and rebuilds entire workspaces after document changes. On every meaningful edit, it is likely to:

- clear workspace caches
- rescan `.tlk` files under the workspace root
- reconstruct all `DocumentInput`s
- rerun parse → resolve → typecheck for the workspace

This is acceptable for tiny projects, but it will scale poorly.

## Evidence

### Workspace caches are cleared broadly

`src/lsp/server.rs` calls `state.workspaces.clear()` in several places, including:

- open/change/close notifications
- watched-file changes
- other document lifecycle events

Representative lines found during audit:

- `src/lsp/server.rs:177`
- `src/lsp/server.rs:192`
- `src/lsp/server.rs:203`
- `src/lsp/server.rs:438`

### Workspace analysis rebuilds from the filesystem

`src/lsp/server.rs:659`

`workspace_analysis()`:

- discovers all `.tlk` files under the root
- merges on-disk files with open in-memory documents
- builds a fresh `Vec<DocumentInput>`
- calls `AnalysisWorkspace::new(docs)`

### `Workspace::new()` runs a full semantic pipeline

`src/analysis/workspace.rs:27`

`Workspace::new()`:

- sorts docs
- clones texts into vectors
- builds `Source::in_memory` values
- constructs a `Driver`
- parses
- resolves names
- typechecks
- clones ASTs and diagnostics into workspace structures

This is not a cheap operation, especially once project size grows.

## Why this matters

LSP latency compounds quickly. Features like:

- hover
- completion
- goto definition
- rename
- diagnostics

all become gated on full-workspace semantic rebuilds if invalidation remains coarse.

Symptoms likely to appear as the workspace grows:

- visible delay after each keystroke burst
- slow diagnostics publication
- stale editor state while background rebuilds run
- unnecessary filesystem traffic
- repeated AST/type cloning overhead

## Root cause

The current architecture treats the analysis workspace as a largely immutable full snapshot. That simplifies correctness, but the invalidation policy is too broad for interactive usage.

There are two distinct costs here:

1. **cache invalidation cost**
   - clearing whole-root analysis state on any change

2. **reconstruction cost**
   - rebuilding semantic state from scratch rather than incrementally

## Recommended improvements

## 1. Stop clearing all workspaces on every edit

Prefer root-scoped invalidation over global invalidation. If only one workspace root changed, only that root's cached analysis should be invalidated.

## 2. Cache root file discovery

`tlk_files_under_root()` should not need to walk the full tree after each edit. Cache the file list and update it only on watched-file events or explicit refresh points.

## 3. Separate open-document text changes from on-disk file discovery

Open buffers already carry their own version numbers. File-system rescans should be rarer than text updates.

## 4. Consider staged incremental analysis

Even without a full incremental compiler, there is room for partial reuse:

- keep parsed ASTs for unchanged files
- keep resolved/typechecked state where possible
- re-run only the affected root or dependency slice

## 5. Reduce cloning in `Workspace::new()`

Current construction eagerly clones text and AST data into multiple vectors/maps. That adds avoidable memory churn.

## Suggested acceptance criteria

Minimum:

- editing one open file does not clear unrelated cached workspace analyses
- file discovery is not repeated on every keystroke-triggered rebuild

Better:

- hover/completion on medium-size workspaces remain subjectively instant
- diagnostics publication occurs without whole-tree rescans on ordinary text edits

Ideal:

- unchanged files reuse parsed/resolved/typechecked state

## Related issues

- [A09](./A09-large-hotspot-files.md): large implementation files raise the cost of safely refactoring LSP internals
- [A10](./A10-repo-hygiene-and-archaeology-debt.md): re-enabling representative benchmarks would make this easier to measure
