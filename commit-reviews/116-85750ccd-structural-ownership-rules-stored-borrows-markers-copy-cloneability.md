# Commit 116: `85750ccd` - Structural ownership rules: stored borrows, markers, copy cloneability

| Field | Value |
|---|---|
| Commit | `85750ccd8d162b7849f5eddef93792d53a7c8f25` |
| Parent reviewed | `4ef76ade365bde36bd84ea8f890f7176b0c881c1` |
| Author date | 2026-07-17T10:53:00-07:00 |
| Author | Pat Nakajima |
| Patch size | 2 files, +84 / -8 |
| Review result | **Request changes** |

## Intent and sequence context

Struct fields and enum payloads typed as borrows reject at build time
(Borrowed-classified views exempt - the view IS the loan); call-site
mut/borrow markers must match the declared parameter modes (ADR 0018);
the copy marker requires a CheapClone value; mut arguments name
mutable places (reworded from unsupported to the rule's voice); and a
global initializer whose view roots in a dying temporary rejects -
provenance-based, so Character literals and global-rooted views stay
legal. rejects_borrowed_global itself stays open as an argued
divergence: this compiler's string literals are immortal statics,
making that exact program sound.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: M: 2.
- Production Rust: 1 files (+84/-3): `src/backend/mir.rs`.
- Tests and test oracles: 1 files (+0/-5): `tests/talk_tests.rs`.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 84 | 3 |
| `tests/talk_tests.rs` | 0 | 5 |

### Representative declarations touched

- `pub(crate) fn build(programs: &[ProgramInput<'_>], entry: Entry) -> Result<Progr`
- `impl<'a> ProgramBuilder<'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `fn reference_flow_corpus_holds() {`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (31s): `run_enforces_capture_list_modes`.
- The persistent `run_enforces_capture_list_modes` failure is inherited from `cabfc772`. Any additional failure attributable to this patch is assessed in Findings below.
- `git diff --check` passed for this commit against its first parent.
- Existing test surfaces changed: `tests/talk_tests.rs`.

## Findings

### 1. [P2] Do not reword an `unsupported` error without changing its constructor

- Location: `src/backend/mir.rs:5011-5014` (tip line numbers)
- Status: **Unresolved latent invariant violation at branch tip**
- Impact: This commit intentionally changes the mut-rvalue message from an unsupported-feature message to the language rule voice, removing `not supported yet`, but leaves the call as `BackendError::unsupported`. Any backend route that reaches this guard in a debug build panics on the constructor assertion rather than returning `a mut argument must name a mutable place`. The simplest source form is currently rejected earlier by the frontend, which makes this latent and entry-path dependent rather than harmless.
- Evidence: Static constructor/message invariant check; this is one of only three current `BackendError::unsupported` calls whose argument lacks the required phrase.
- Recommended correction: Change this call to `BackendError::new`, and add a backend-level regression test that exercises the guard without relying on frontend rejection.

## Disposition

Do not merge this commit as currently represented at the branch tip until the unresolved finding above is corrected.
