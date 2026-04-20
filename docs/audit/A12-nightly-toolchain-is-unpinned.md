# A12: Nightly toolchain is unpinned

**Severity:** Low-medium  
**Area:** build reproducibility / toolchain stability  
**Primary files:** `rust-toolchain.toml`, `www/rust-toolchain.toml`, `src/lib.rs`

## Summary

The project depends on nightly Rust and multiple unstable feature gates, but the toolchain files specify plain `nightly` rather than a pinned nightly date. That increases the chance of surprising breakage as nightly evolves.

## Evidence

### Toolchain files

- `rust-toolchain.toml`
- `www/rust-toolchain.toml`

Both currently specify:

```toml
[toolchain]
channel = "nightly"
```

### The crate uses unstable features

`src/lib.rs` enables many nightly-only features, including examples such as:

- `box_patterns`
- `associated_type_defaults`
- `try_blocks`
- `try_trait_v2`
- `never_type`
- and others

## Why this matters

An unpinned nightly means:

- today's working build can break tomorrow without any code changes
- CI and local machines may observe different compiler behavior
- lint output can drift unexpectedly
- bisecting regressions becomes harder
- onboarding becomes more fragile

This matters more when the project uses a wide surface area of unstable functionality.

## Recommended fix

Pin the nightly channel to a specific date, for example:

```toml
[toolchain]
channel = "nightly-YYYY-MM-DD"
```

Then update deliberately when needed.

## Suggested process

1. pick a known-good nightly
2. update both root and `www/` toolchain files together if they must stay aligned
3. document the update process in the repo README or contributing docs
4. periodically bump the pinned nightly intentionally rather than continuously tracking head

## Acceptance criteria

- Nightly toolchains are pinned to explicit dates.
- CI and local development use the same compiler snapshot by default.
- Toolchain upgrades become deliberate events with visible diff/review.

## Related issues

- [A11](./A11-clippy-not-enforced-in-ci.md): lint and compiler behavior are more meaningful when the toolchain is stable
- [A10](./A10-repo-hygiene-and-archaeology-debt.md): better project documentation should include toolchain expectations
