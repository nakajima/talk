# How the language server works

This directory implements `talk lsp --stdio` on `async-lsp`. It adapts the
frontend analysis modules to LSP protocol types; parsing, desugaring, name
resolution, type checking, and structured diagnostics remain in the shared
frontend pipeline.

## Division of labor

`src/analysis` owns protocol-independent editor analysis:

- `workspace.rs` checks open documents in lenient mode, follows imported files,
  and retains text, source-faithful ASTs, resolved names, types, and diagnostics;
- `hover.rs` reports binder schemes and inferred expression types;
- `completion.rs` provides scope- and type-backed completions;
- `definition.rs` and `rename.rs` resolve symbols across files and imports.

`src/lsp` translates those products. `server.rs` manages requests, document
lifecycles, debounce, and diagnostic publication. `document.rs` owns conversion
between LSP UTF-16 positions and internal byte offsets.

## Current features

- parser, name-resolution, and type diagnostics with stable diagnostic codes;
- type and scheme hover;
- go-to-definition and workspace rename;
- full-document semantic tokens;
- scope, member, and protocol-requirement completion;
- conservative structured-diagnostic code actions described by ADR 0028;
- document formatting.

Ownership diagnostics and ownership inlay hints are absent in the frontend-only
compiler. The server does not advertise an inlay-hint provider.

## Notes

UTF-16 conversion belongs only in `document.rs` and `src/common/text.rs`. Tests
at the bottom of `server.rs` construct real in-memory workspaces so protocol
adaptation is checked against the frontend rather than mocks.
