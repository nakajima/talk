# What this directory is

Terminal presentation for the compiler. The commands themselves are
defined in `src/bin/talk.rs` (clap); this directory holds what they
share:

- `diagnostics.rs` — rendering compiler errors for humans: source
  excerpt, caret underline, line/column, colors (suppressed under
  `NO_COLOR`), plus a JSON form for editors and scripts
  (`talk check --json`).
- `repl.rs` — the interactive REPL frontend: line editing, history,
  live syntax highlighting, and tab completion (backed by
  `src/analysis`). The REPL's *semantics* — how declarations persist
  across lines and how results are evaluated and rendered — live in
  `src/repl.rs` at the crate root, so they're testable without a
  terminal.

The pipeline these commands drive is documented in
`src/compiling/README.md`.
