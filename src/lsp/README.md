# How the language server works

This directory implements the LSP server (`talk lsp --stdio`), built
on `async-lsp`. It's a thin protocol layer: the actual analysis —
parsing, name resolution, type checking — is the same pipeline the
compiler runs (see `src/compiling`), packaged for editors by
`src/analysis`.

## The division of labor with `src/analysis`

`src/analysis` is the editor-facing API with no protocol types in it:

- `workspace.rs` — `AnalysisWorkspace` takes the open documents,
  runs the driver in lenient mode (a file that doesn't parse yields
  diagnostics and an empty AST instead of aborting) with comments
  preserved, and keeps the per-document texts, ASTs, resolved names,
  type information, and diagnostics. It also supports core overrides:
  open a file from `core/` and the workspace swaps it in for the
  embedded copy, so the standard library is hackable with live
  feedback.
- `hover.rs` — type-at-cursor: find the smallest node at the offset,
  prefer a named binder's full signature (schemes), fall back to the
  node's inferred type.
- `completion.rs` — scope-based completions from resolved names, and dot member completions from the checker's type output/catalog.
- `ownership.rs` — editor-facing ownership facts (move/borrow/drop)
  from the post-type-check ownership pass, rendered as hover detail
  lines and inlay hints, with no protocol types.

`src/lsp` then translates: `server.rs` wires protocol requests to
those functions, manages document lifecycles and a debounce for
re-analysis, and publishes diagnostics. `document.rs` owns the
position math (LSP speaks UTF-16 line/character; everything internal
is byte offsets) and incremental text edits.

## What the server provides

- **Diagnostics** — parser, name-resolution, type, and ownership errors, on open
  and (debounced) on change. Whatever message the compiler produces
  is what the editor shows, so improvements to checker errors are
  improvements here for free.
- **Hover** — signatures for bindings (`<T0, T1>(T0) -> T1 where
  T0.go: () -> T1`), inferred types for expressions.
- **Inlay hints** (`ownership_inlay_hints_lsp` in `server.rs`) —
  move/borrow/drop annotations from the ownership pass, rendered
  inline (see `src/analysis/ownership.rs`).
- **Go to definition** (`goto_definition.rs`) — symbol under cursor →
  its declaration site, including through imports, variants in
  patterns, and members.
- **Rename** (`rename.rs`) — every node resolving to the symbol gets
  the edit; cross-file within the workspace.
- **Semantic tokens** (`semantic_tokens.rs`) — full-document
  highlighting classified from the AST (see
  `src/parsing/highlighter.rs`).
- **Completions** (`completion.rs`) — translation of the analysis
  items to protocol items.
- **Code actions** (`compute_code_actions` in `server.rs`) — quick
  fixes keyed off diagnostic messages: add a missing `import` for an
  undefined name that's public in another workspace file, and the
  ambiguous-member fix that rewrites `x.m(args)` into the explicit
  `P.m(x, args)` form, one action per candidate protocol.

## Notes

The position-mapping helpers in `document.rs` and
`src/common/text.rs` are the only places UTF-16 exists; keep it that
way. The `SLOP` file marks this directory as a place where
experimentation is welcome — protocol plumbing is not architecture.
Tests live at the bottom of `server.rs` and build real workspaces
from in-memory documents (`workspace_for_docs`), so hover, code
actions, and rename are tested against the actual pipeline rather
than mocks.
