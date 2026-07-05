# How the language server works

This directory implements the LSP server (`talk lsp --stdio`), built on
`async-lsp`. It is a protocol layer: the actual analysis — parsing,
desugaring, name resolution, type checking, flow facts, and diagnostics —
is the same pipeline the compiler runs (see `src/compiling`), packaged for
editors by `src/analysis`.

## The division of labor with `src/analysis`

`src/analysis` is the editor-facing API with no protocol types in it:

- `src/analysis/workspace.rs` — `Workspace` takes open documents, runs the driver in
  lenient mode (a file that does not parse yields diagnostics and an empty
  AST instead of aborting) with comments preserved, and keeps per-document
  texts, source-faithful ASTs, resolved names, type information, flow facts,
  and diagnostics. It also follows files discovered through imports. When
  the open documents are core files marked `// no-core`, it type-checks the
  full core set with those open documents as overrides, so the standard
  library is hackable with live feedback.
- `src/analysis/hover.rs` — type-at-cursor: find the smallest node at the offset, prefer
  a named binder's full scheme/signature, fall back to the node's inferred
  type, and append ownership details from the flow facts when available.
- `src/analysis/completion.rs` — scope-based completions from resolved names, and dot
  member completions from the checker's type output/catalog.
- `src/analysis/ownership.rs` — editor-facing ownership/flow facts (move, borrow, clone,
  drop) rendered as hover detail lines and inlay hints, with no protocol
  types.

`src/lsp` then translates: `server.rs` wires protocol requests to those
functions, manages document lifecycles and a debounce for re-analysis, and
publishes diagnostics. `document.rs` owns the position math (LSP speaks
UTF-16 line/character; everything internal is byte offsets) and incremental
text edits.

## What the server provides

- **Diagnostics** — parser, name-resolution, type, and flow/ownership
  errors, on open and (debounced) on change. Whatever message the compiler
  produces is what the editor shows.
- **Hover** — signatures for bindings (for example
  `<T0, T1>(T0) -> T1 where T0.go: () -> T1`), inferred types for
  expressions, and ownership details.
- **Inlay hints** (`ownership_inlay_hints_lsp` in `server.rs`) —
  move/borrow/clone/drop annotations from `src/analysis/ownership.rs`.
- **Go to definition** (`goto_definition.rs`) — symbol under cursor to its
  declaration site, including through relative imports, import lists,
  variants in patterns, members, effects, type parameters, and core symbols
  when core analysis is available.
- **Rename** (`rename.rs`) — every node resolving to the symbol gets the
  edit; cross-file within the workspace, including import specifiers while
  preserving aliases correctly.
- **Semantic tokens** (`semantic_tokens.rs`) — full-document highlighting
  classified from the AST/highlighter (`src/parsing/highlighter.rs`).
- **Completions** (`completion.rs`) — translation of analysis completion
  items to LSP completion items; dot completion is triggered by `.`.
- **Code actions** (`compute_code_actions` in `server.rs`) — quick fixes
  keyed off diagnostic messages: add a missing `use { name } from ...` for
  an undefined name that is public in another workspace file, and rewrite an
  ambiguous member call `x.m(args)` into the explicit protocol-static form
  `P.m(x, args)`, one action per candidate protocol.

## Notes

The position-mapping helpers in `document.rs` and `src/common/text.rs` are
the only places UTF-16 exists; keep it that way. The `SLOP` file marks this
directory as a place where experimentation is welcome — protocol plumbing is
not architecture. Tests live at the bottom of `server.rs` and build real
workspaces from in-memory documents (`workspace_for_docs`), so hover, code
actions, go-to-definition, inlay hints, and rename are tested against the
actual pipeline rather than mocks.
