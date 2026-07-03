# Panic audit

Goal: the LSP process must not exit because compiler, parser, formatter, or analysis code panicked. If an internal invariant fails, the user should see an LSP error message and a diagnostic instead of a dead server.

## Current guardrail

`src/lsp/server.rs` wraps LSP-facing work with `recover_lsp(...)`:

- workspace analysis
- core symbol analysis
- formatting
- rename, hover, definition, completion, inlay hints, code actions
- semantic token collection
- document change application

On panic, the server:

1. catches the unwind,
2. sends `window/showMessage`,
3. publishes a `talk-lsp` diagnostic on the active document when possible,
4. returns an empty or missing result for that request.

LSP startup paths now report errors to stderr instead of using `unwrap` or `expect`.

## Enforcement command

Use this for production targets:

```sh
cargo clippy --features cli -- -D clippy::unwrap_used -D clippy::expect_used -D clippy::panic -D clippy::todo
```

This currently passes for production targets. Test code still uses `unwrap`, `expect`, and `panic` freely.

## Remaining explicit production allowances

These are the remaining `#[allow(clippy::...)]` sites outside test-only files. They should stay visible until they are either removed or replaced with diagnostic-returning APIs.

- `src/compiling/core.rs` and `src/compiling/stdlib.rs`
  - Bootstrap core and stdlib with `unwrap` plus an invariant `assert` for diagnostics.
  - LSP catches failures at the workspace-analysis boundary.
  - Better end state: expose fallible core/stdlib compile APIs and thread errors into diagnostics.

- `src/parsing/parser.rs`, `src/name_resolution/name_resolver.rs`, `src/name_resolution/decl_declarer.rs`
  - Parser/resolver scope invariants use `expect`/`panic` internally.
  - Better end state: convert resolver/parser invariant failures into internal diagnostics.

- `src/parsing/node.rs`, `src/parsing/node_kinds/stmt.rs`, `src/parsing/name.rs`, `src/name_resolution/symbol.rs`
  - Conversion helpers panic when called with the wrong variant.
  - Better end state: use `TryFrom`/`Option` in LSP-facing paths and reserve panicking conversions for tests only.

## Policy

- No new LSP request/notification should call analysis, formatting, parser, resolver, or compiler code without `recover_lsp` or an equivalent fallible path.
- No new production `unwrap`, `expect`, `panic`, `todo`, or `unimplemented` without documenting why it cannot be user-triggered.
- Prefer returning diagnostics or `Option`/`Result` over panicking on malformed user input.
