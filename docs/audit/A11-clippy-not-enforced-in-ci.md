# A11: Clippy is not enforced in CI

**Severity:** Medium-low  
**Area:** code quality enforcement / CI discipline  
**Primary files:** `.github/workflows/rust.yml`, `src/lib.rs`

## Summary

The repository already expresses strong lint intentions in code, but CI currently runs only build and test. As a result, `cargo clippy --workspace --all-targets` can fail on production code without blocking integration.

## Evidence

### CI workflow contents

`.github/workflows/rust.yml` currently runs:

- `cargo build --verbose`
- `cargo test --verbose`

No clippy step is present.

### Clippy currently fails

Audit command:

- `cargo clippy --workspace --all-targets`

This failed on production `unwrap()` usage, including:

- `src/ir/lowerer.rs:1143`
- `src/name_resolution/name_resolver.rs:423`

It also surfaced additional maintainability warnings.

### The codebase already wants stricter behavior

`src/lib.rs` contains:

- `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`
- `#![cfg_attr(not(test), deny(clippy::expect_used))]`
- other deny-level clippy policies

That indicates a clear intent to keep panic-style shortcuts out of production code.

## Why this matters

Without CI enforcement:

- lint regressions slip in silently
- stated code-quality policy loses credibility
- developers get inconsistent feedback depending on local habits
- panic/unwrap usage can accumulate in production paths

This is especially relevant in a compiler/runtime project where error handling and invariants matter a lot.

## Recommended fix

Add at least one CI step:

- `cargo clippy --workspace --all-targets -- -D warnings`

If warning volume is currently too high, use a staged approach:

1. add clippy in non-blocking mode or with current deny-level constraints only
2. fix existing failures
3. tighten to blocking mode

Also consider adding:

- `cargo fmt --check`

## Acceptance criteria

- CI fails when production clippy-denied lints fail.
- The current clippy failures are addressed or intentionally scoped.
- Local and CI expectations match.

## Related issues

- [A07](./A07-cli-error-handling-and-ux-inconsistencies.md): several CLI polish issues would be easier to prevent with broader automated hygiene
- [A12](./A12-nightly-toolchain-is-unpinned.md): pinning the toolchain reduces lint drift across environments
