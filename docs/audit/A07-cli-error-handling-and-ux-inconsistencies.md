# A07: CLI error handling and UX inconsistencies

**Severity:** Medium  
**Area:** CLI / user experience / operational polish  
**Primary file:** `src/bin/talk.rs`

## Summary

The CLI works, but its error-handling style is inconsistent. Some commands return diagnostics, some panic on ordinary user errors, some silently bail out, and a few small correctness/clarity issues make the interface feel less polished than the underlying compiler deserves.

## Evidence

Representative examples from `src/bin/talk.rs`:

### Panic-based command flows

Several commands chain `.unwrap()` through normal compiler stages:

- parse
- resolve
- typecheck
- lower

Examples:

- `Parse` path
- `Ir` path
- `Run` path
- `Debug` path

These are fine for quick local tools, but they produce poor CLI behavior for users.

### Panic on read failures

Helper functions use `panic!` for normal IO failures:

- reading files
- reading stdin

Ordinary bad-input cases should surface as user-facing errors and exit codes, not stack-style crashes.

### Silent failure path

`Check` uses:

- `let Some(workspace) = Workspace::new(docs) else { return; };`

If workspace construction fails entirely, the command just returns without output. That is confusing in automation and shells.

### Hover argument message inversion

`parse_hover_query()` reports:

- `"--line requires --column"`
- `"--column requires --line"`

But the current implementation applies the line error to the column absence and vice versa. The validation logic is right; the messages are effectively swapped.

### Duplicate cfg attribute

The entrypoint begins with duplicate `#[cfg(feature = "cli")]` lines. Harmless, but unnecessary noise.

### Inconsistent module naming

`Run` builds the lowered module with the display name `"talkin"` rather than the more obvious `"talk"` or the user/module-derived name. This may be harmless, but it looks accidental and undermines confidence.

## Why this matters

A compiler CLI is part of the product surface. Panic-heavy UX makes the tool feel more experimental than it needs to.

Problems caused by the current style:

- poor shell/CI ergonomics
- confusing failure modes
- weak machine-consumability for wrappers/scripts
- harder debugging when failures bypass normal diagnostic paths

## Recommended improvements

## 1. Standardize command results

Have subcommand handlers return `Result<(), Error>` and let `main` map them to:

- user-friendly stderr output
- explicit exit codes

Existing dependencies already include `anyhow`, so this can be done without introducing a new crate.

## 2. Reserve panics for programmer errors

File-not-found, parse errors, type errors, and workspace-construction failures are normal operational outcomes.

## 3. Make `check` fail loudly when workspace construction fails

Return a non-zero exit and a clear message instead of silently returning.

## 4. Fix small correctness/polish issues

- swap the hover validation messages so they match the missing flag
- remove duplicate cfg attributes
- confirm whether `"talkin"` is intentional; if not, normalize it

## 5. Reuse diagnostic rendering paths

Wherever possible, CLI commands should route failures through the same diagnostic-oriented reporting style used elsewhere in the codebase.

## Acceptance criteria

- No normal user error path causes the CLI to panic.
- `check`, `hover`, `run`, and `ir` all return clear, stable exit semantics.
- Hover argument error text matches the actual missing argument.
- Minor entrypoint inconsistencies are cleaned up.

## Related issues

- [A06](./A06-interpreter-runtime-contract-is-panic-heavy.md): runtime panics currently bubble through user-facing CLI paths
- [A11](./A11-clippy-not-enforced-in-ci.md): stricter automated hygiene would help prevent regressions here
