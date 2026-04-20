# Audit follow-up docs

This directory contains detailed write-ups for each issue identified during the 2026-04-07 codebase audit.

## Validation performed

The audit was grounded in source inspection plus command-level validation:

- `cargo test --workspace`
  - Result: **2 failed**, **673 passed**, **9 ignored** in `talk`'s main test suite
  - Failing tests:
    - `ir::interpreter::tests::interprets_io_open_and_close`
    - `ir::interpreter::tests::interprets_io_open_write_read`
- `cargo clippy --workspace --all-targets`
  - Result: **failed** on production `unwrap()` usage and reported additional maintainability warnings

## Issues

### High priority

1. [A01: External module identity and import collisions](./A01-external-module-identity-and-import-collisions.md)
2. [A02: Interpreter string/path I/O mismatch](./A02-interpreter-string-path-io-mismatch.md)
3. [A03: User-reachable `todo!()` / `unimplemented!()` paths](./A03-user-reachable-todo-and-unimplemented-paths.md)
4. [A04: LSP full-workspace rebuild behavior](./A04-lsp-full-workspace-rebuild-behavior.md)

### Medium priority

5. [A05: Interpreter byte conversion overhead](./A05-interpreter-byte-conversion-overhead.md)
6. [A06: Interpreter runtime contract is panic-heavy](./A06-interpreter-runtime-contract-is-panic-heavy.md)
7. [A07: CLI error handling and UX inconsistencies](./A07-cli-error-handling-and-ux-inconsistencies.md)
8. [A08: `CaptureIO::read_stdio` does not match real stdio semantics](./A08-captureio-read-stdio-semantics.md)
9. [A09: Large hotspot files reduce clarity and change safety](./A09-large-hotspot-files.md)
10. [A10: Repo hygiene and archaeology debt](./A10-repo-hygiene-and-archaeology-debt.md)

### Lower priority but still worth addressing

11. [A11: Clippy is not enforced in CI](./A11-clippy-not-enforced-in-ci.md)
12. [A12: Nightly toolchain is unpinned](./A12-nightly-toolchain-is-unpinned.md)

## Suggested remediation order

1. Fix A02 so the test suite is green again.
2. Fix A01 before external-module/package work expands further.
3. Replace A03 panic placeholders with real diagnostics or implementations.
4. Improve A04 before the LSP is asked to scale to larger workspaces.
5. Address A05 and A06 together as the interpreter hardening/performance pass.
6. Clean up A07, A11, and A12 as engineering-discipline follow-ups.
7. Use A09 and A10 as the maintainability pass after correctness issues are under control.

## Notes

- These docs are intentionally specific and action-oriented.
- Line numbers and file references were accurate at audit time and may drift as the code changes.
- Several issues are related; cross-links are included where useful.
