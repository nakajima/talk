# Editor analysis

This directory provides editor-facing frontend analysis without LSP protocol
types. `Workspace` runs parsing, name resolution, and type checking leniently
over open documents while retaining source-faithful ASTs, text, resolved names,
types, and structured diagnostics.

Modules provide type and scheme hover, scope- and type-backed completion,
go-to-definition, and rename. The same interface serves the LSP, C/Swift
embedding, wasm tooling, REPL completion, and tests.

Ownership-flow facts and ownership inlay hints are intentionally absent while
the compiler is frontend-only. See `src/lsp/README.md` for protocol adaptation
and `src/compiling/README.md` for the frontend pipeline.
