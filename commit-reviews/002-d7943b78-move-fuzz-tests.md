# Commit 002: `d7943b78` - move fuzz tests

| Field | Value |
|---|---|
| Commit | `d7943b7827945d5f71a05ea4ef76a0ab3eb837e9` |
| Parent reviewed | `fc4696b1631c9b29f0f95006f797f39b4fad9780` |
| Author date | 2026-07-12T22:56:26-07:00 |
| Author | Pat Nakajima |
| Patch size | 8 files, +37 / -26 |
| Review result | **No commit-local blocker identified** |

## Intent and sequence context

No explanatory commit body was provided; intent is inferred from the subject and patch.

This belongs to the pre-reset implementation and is superseded by `a1d20d27` (commit 005 in this review set). It is still reviewed as an atomic historical patch.

## Patch analysis

- File operations: M: 7, R: 1.
- Production Rust: 3 files (+18/-17): `src/compiling/driver.rs`, `src/lambda_g/balance.rs`, `src/lib.rs`.
- Tests and test oracles: 1 files (+4/-4): `src/fuzz_tests.rs => tests/fuzz.rs`.
- Build, packaging, and CI: 2 files (+8/-0): `.github/workflows/ci.yml`, `Cargo.toml`.
- Documentation and plans: 2 files (+7/-5): `docs/ownership-soundness-plan.md`, `docs/single-source-of-truth-plan.md`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/compiling/driver.rs` | 12 | 10 |
| `src/lambda_g/balance.rs` | 6 | 4 |
| `docs/ownership-soundness-plan.md` | 6 | 4 |
| `src/fuzz_tests.rs => tests/fuzz.rs` | 4 | 4 |
| `Cargo.toml` | 6 | 0 |
| `src/lib.rs` | 0 | 3 |
| `docs/single-source-of-truth-plan.md` | 1 | 1 |
| `.github/workflows/ci.yml` | 2 | 0 |

### Representative declarations touched

- `impl Driver<Typed> {`
- `impl Driver<Lowered> {`
- `pub fn verify_balance(p: &Program, main: Label, entry_funcs: &FxHashSet<Label>)`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (4s).
- Historical checkout: `cargo test --locked --quiet` passed at this exact commit (25s).
- Commit-specific CI command: `cargo test --test fuzz --features fuzz-tests --locked --quiet` passed at this exact commit (5 tests).
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `src/fuzz_tests.rs => tests/fuzz.rs`.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No blocker in this patch beyond the sequence/supersession caveat above. Preserve it only if retaining the historical staging is valuable; otherwise squash superseded implementation phases before merge.
