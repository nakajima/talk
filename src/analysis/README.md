# What this directory is

The editor-facing analysis API, with no LSP protocol types in it:
`AnalysisWorkspace` (run the compiler pipeline leniently over a set of
open documents and keep texts, ASTs, resolved names, types, and
diagnostics), `hover.rs` (type at a position), and `completion.rs`
(scope-based completions).

It exists as a separate layer so the same functionality serves the
LSP server, the REPL's tab completion, and tests, without any of them
touching protocol types. The full picture of how it's used — and the
division of labor with the protocol layer — is documented in
`src/lsp/README.md`; the pipeline it runs is documented in
`src/compiling/README.md`.
