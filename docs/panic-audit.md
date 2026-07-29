# Panic audit

Status: current policy; explicit allowance inventory refreshed 2026-07-28 after
the self-hosted frontend cutover.

Goal: the LSP process must not exit because compiler, frontend, formatter, or
analysis code panicked. If an internal invariant fails, the user should see an
LSP error message and a diagnostic instead of a dead server.

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

This is the target policy, but it is not currently green. On 2026-07-28 the
command failed with 32 production `expect`/`panic` violations. Test code still
uses `unwrap`, `expect`, and `panic` freely.

## Explicit production allowances

These are the current `#[allow(clippy::...)]` sites outside test-only code. They
should stay visible until they are removed or replaced with
diagnostic-returning APIs.

- `src/compiling/core.rs` and `src/compiling/stdlib.rs`
  - Bootstrap core and stdlib with `unwrap` plus an invariant `assert` for diagnostics.
  - LSP catches failures at the workspace-analysis boundary.
  - Better end state: expose fallible core/stdlib compile APIs and thread errors into diagnostics.

- `src/name_resolution/name_resolver.rs` and
  `src/name_resolution/decl_declarer.rs`
  - Resolver scope invariants use `expect` internally.
  - Better end state: convert user-reachable resolver invariant failures into
    internal diagnostics.

- `src/parsing/node.rs`, `src/parsing/node_kinds/stmt.rs`,
  `src/parsing/name.rs`, and `src/name_resolution/symbol.rs`
  - Conversion helpers panic or expect the correct internal variant.
  - Better end state: use `TryFrom`/`Option` in LSP-facing paths and reserve
    panicking conversions for proven internal invariants.

- `src/backend/optimize/inline_small.rs`
  - The inliner expects a value it has just classified as present.
  - Keep the allowance local to that invariant; backend failures reached from
    the LSP remain behind `recover_lsp`.

## Unresolved lint violations

The 2026-07-28 enforcement run found unallowed production panics in these
areas:

- formatter generic-shape assertions in `src/parsing/formatter.rs`;
- typed-fact and CFG invariants in `src/backend/mir/mod.rs`;
- module and stdlib registration invariants in `src/compiling/driver.rs`,
  `module.rs`, `package.rs`, and `stdlib.rs`;
- typed-program construction invariants in
  `src/compiling/typed_program/build.rs`;
- checked argument and core-shape assumptions in `src/types/generate/`.

These are audit findings, not approved allowances. Either make them fallible or
add a narrowly documented allowance after proving they cannot be user-triggered.

## Policy

- No new LSP request/notification should call analysis, formatting, parser, resolver, or compiler code without `recover_lsp` or an equivalent fallible path.
- No new production `unwrap`, `expect`, `panic`, `todo`, or `unimplemented` without documenting why it cannot be user-triggered.
- Prefer returning diagnostics or `Option`/`Result` over panicking on malformed user input.
