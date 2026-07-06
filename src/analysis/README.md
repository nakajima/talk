# What this directory is

The editor-facing analysis API, with no LSP protocol types in it:
`Workspace` (runs the compiler pipeline leniently over open documents,
keeps the source-faithful ASTs the compile pipeline later lowers away,
and stores texts, resolved names, types, flow facts, and diagnostics),
`hover.rs` (type or scheme at a position, plus ownership details),
`ownership.rs` (move/borrow/clone/drop hover details and inlay hints from
`FlowFacts`), and `completion.rs` (scope-based completions,
type-backed member completions, and conformance requirement completions).

It exists as a separate layer so the same functionality serves the
LSP server, the REPL's tab completion, and tests, without any of them
touching protocol types. The full picture of how it's used — and the
division of labor with the protocol layer — is documented in
`src/lsp/README.md`; the pipeline it runs is documented in
`src/compiling/README.md`.
